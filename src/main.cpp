// include this first to fix macro redef warnings
#include <pyconfig.h>

#include <cassert>
#include <cstdint>
#include <cstring>
#include <codecvt>
#include <ctime>
#include <filesystem>
#include <fstream>
#include <list>
#include <locale>
#include <string>
#include <vector>
#include <map>
#include <memory>
#include <optional>

#include <boost/version.hpp>
#pragma GCC diagnostic push
#if BOOST_VERSION < 108100
#  pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#endif
#include <boost/config.hpp>
#include <boost/date_time.hpp>
#include <boost/algorithm/string/replace.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/algorithm/string/classification.hpp>
#include <boost/filesystem.hpp>
#pragma GCC diagnostic pop

#include <irods/rodsErrorTable.h>
#include <irods/irods_default_paths.hpp>
#include <irods/irods_error.hpp>
#include <irods/irods_exception.hpp>
#include <irods/irods_logger.hpp>
#include <irods/irods_re_plugin.hpp>
#include <irods/irods_re_structs.hpp>
#include <irods/irods_re_ruleexistshelper.hpp>
#include <irods/irods_re_serialization.hpp>
#include <irods/irods_ms_plugin.hpp>
#include <irods/irods_server_properties.hpp>
#include <irods/msParam.h>
#include <irods/rsExecMyRule.hpp>

#include "irods/private/re/python.hpp"

#include <patchlevel.h>
#pragma GCC diagnostic push
#if PY_VERSION_HEX < 0x030400A2
#  pragma GCC diagnostic ignored "-Wregister"
#endif
#if PY_VERSION_HEX >= 0x03090000 && BOOST_VERSION < 107500
#  pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#endif
#include <boost/python/slice.hpp>
#include <boost/python/module_init.hpp>
#pragma GCC diagnostic pop

#include <fmt/format.h>

irods::ms_table& get_microservice_table();

// writeLine is not in the microservice table in 4.2.0 - #3408
int writeLine(msParam_t*, msParam_t*, ruleExecInfo_t*);

static int remote_exec_msvc(msParam_t* _pd, msParam_t* _pa, msParam_t* _pb, msParam_t* /*_pc*/, ruleExecInfo_t* _rei)
{
	execMyRuleInp_t exec_inp;
	memset(&exec_inp, 0, sizeof(exec_inp));
	rstrcpy(exec_inp.outParamDesc, ALL_MS_PARAM_KW, LONG_NAME_LEN);

	char tmp_str[LONG_NAME_LEN];
	rstrcpy(tmp_str, static_cast<char*>(_pd->inOutStruct), LONG_NAME_LEN);
	parseHostAddrStr(tmp_str, &exec_inp.addr);

	std::string rule_text = "@external\n";
	rule_text += static_cast<char*>(_pb->inOutStruct);
	snprintf(exec_inp.myRule, META_STR_LEN, "%s", rule_text.c_str());

	// TODO:
	// It is not yet known whether execCondition is actually used by rsExecMyRule or
	// any functions it calls. If in resolution of [irods/irods#6567] we find it is
	// unused, the following addKeyVal call may be unnecessary.
	addKeyVal(&exec_inp.condInput, "execCondition", static_cast<char*>(_pa->inOutStruct));

	auto taggedValues = getTaggedValues(static_cast<char*>(_pa->inOutStruct));
	auto it = taggedValues.find("INST_NAME");
	if (it != taggedValues.end()) {
		addKeyVal(&exec_inp.condInput, INSTANCE_NAME_KW, it->second.front().c_str());
		taggedValues.erase(it);
	}

	msParamArray_t* out_arr = NULL;
	return rsExecMyRule(_rei->rsComm, &exec_inp, &out_arr);
} // remote_exec_msvc

namespace bp = boost::python;
namespace sfs = std::filesystem;
namespace bfs = boost:filesystem;

namespace
{
	static BOOST_FORCEINLINE constexpr const char* const rule_engine_name = "python";

	using log_re = irods::experimental::log::rule_engine;

	const std::string ELEMENT_TYPE = "ELEMENT_TYPE";
	const std::string STRING_TYPE = "STRING_TYPE";
	const std::string STRING_VALUE_KEY = "STRING_VALUE_KEY";
	const std::string IRODS_ERROR_PREFIX = "[iRods__Error__Code:";

	const std::string STATIC_PEP_RULE_REGEX = "ac[^ ]*";
	const std::string DYNAMIC_PEP_RULE_REGEX = "[^ ]*pep_[^ ]*_(pre|post)";

#if PY_VERSION_HEX >= 0x03080000
	using pypath_string = std::wstring;
	// Python uses a lot of wchar_t-based strings.
	// Python provides PyConfig_SetBytesString for converting from char-based strings
	// but it is locale-dependant. Instead, we handle it ourselves.

	// (w)string converter for non-paths
	// NOTE: codecvt is deprecated,
	//       but stdlib has no replacement for it in C++20
	//       and we don't want a direct dependency on boost.locale
	// https://stackoverflow.com/a/18597384/6278710
	const std::wstring_convert<std::codecvt_utf8<wchar_t>> wstring_converter;

	static BOOST_FORCEINLINE pypath_string& get_pypath_string(const sfs::path& path) { return path.generic_wstring(); }
	static BOOST_FORCEINLINE pypath_string& get_pypath_string(const bfs::path& path) { return path.generic_wstring(); }
#else
	using pypath_string = std::string;

	static BOOST_FORCEINLINE pypath_string& get_pypath_string(const sfs::path& path) { return path.generic_string(); }
	static BOOST_FORCEINLINE pypath_string& get_pypath_string(const bfs::path& path) { return path.generic_string(); }
#endif

	static BOOST_FORCEINLINE pypath_string& get_pypath_string(const std::string& path)
	{
		if (path == "$IRODS_CONFIG_DIRECTORY$") {
			return get_pypath_string(irods::get_irods_config_directory());
		}
		return get_pypath_string(sfs::path{path});
	}

	// Data we hang onto for the interpreter
	namespace python_state
	{
		// Thread state object for main Python interpreter
		PyThreadState* ts_main;

#if PY_VERSION_HEX >= 0x03080000
		// List of default module search paths
		std::vector<std::wstring> default_module_search_paths;
		// Whether or not default_module_search_paths is populated
		bool default_module_search_paths_set = false;
#endif
	} //namespace python_state

	namespace plugin_configuration
	{
		namespace defaults
		{
			const std::vector<const std::string> re_pep_regex_set{STATIC_PEP_RULE_REGEX, DYNAMIC_PEP_RULE_REGEX};

			namespace interpreter
			{
#if PY_VERSION_HEX >= 0x03080000
				const int isolated = 1;

				const int dev_mode = 0;
				const int use_environment = 0;
				const int utf8_mode = 1;
				const int verbose = 0;
				const std::optional<unsigned long> hash_seed = std::nullopt;
#if PY_VERSION_HEX >= 0x030C0000
				const std::optional<int> int_max_str_digits = std::nullopt;
				const int perf_profiling = 0;
#endif
				const std::optional<std::vector<std::wstring>> xoptions = std::nullopt;

				const std::optional<int> configure_locale = std::nullopt;
				const std::optional<int> coerce_c_locale = std::nullopt;
				const std::optional<int> coerce_c_locale_warn = std::nullopt;

				const std::optional<int> site_import = std::nullopt;
				const int user_site_directory = 0; // irods user probably doesn't have a proper home directory

				const std::optional<int> optimization_level = std::nullopt;
				const std::optional<int> write_bytecode = std::nullopt;
				const std::optional<pypath_string> pycache_prefix = std::nullopt;
				const std::optional<std::wstring> check_hash_pycs_mode = std::nullopt;

				const std::optional<pypath_string> base_prefix = std::nullopt;
				const std::optional<pypath_string> prefix = std::nullopt;
				const std::optional<pypath_string> base_exec_prefix = std::nullopt;
				const std::optional<pypath_string> exec_prefix = std::nullopt;
				const std::optional<pypath_string> base_executable = std::nullopt;
				const std::optional<pypath_string> executable = std::nullopt;

				const std::optional<std::wstring> filesystem_encoding = std::nullopt;
				const std::optional<std::wstring> filesystem_errors = std::nullopt;

				const std::optional<std::wstring> stdio_encoding = std::nullopt;
				const std::optional<std::wstring> stdio_errors = std::nullopt;

				const std::optional<int> buffered_stdio = std::nullopt;
				const std::optional<int> configure_c_stdio = std::nullopt;

				const std::optional<int> bytes_warning = std::nullopt;
				const std::optional<int> pathconfig_warnings = std::nullopt;
#if PY_VERSION_HEX >= 0x030A0000
				const std::optional<int> warn_default_encoding = std::nullopt;
#endif
				const std::optional<std::vector<std::wstring>> warnoptions = std::nullopt;

#ifdef Py_DEBUG
				const int parser_debug = 0;
#endif
				const int tracemalloc = 0;
				const int import_time = 0;

				const std::optional<std::vector<pypath_string>> module_search_paths = std::nullopt;
#endif

				namespace additional_module_search_paths
				{
					const std::optional<std::vector<pypath_string>> prepend = std::nullopt;
					const std::optional<std::vector<pypath_string>> append = std::nullopt;
				} //namespace additional_module_search_paths
			} //namespace interpreter
		} //namespace defaults

		std::vector<const std::string> re_pep_regex_set{defaults::re_pep_regex_set};

		namespace interpreter
		{
#if PY_VERSION_HEX >= 0x03080000
			// Whether the interpreter is configured in isolated mode.
			// If 0, interpreter configuration is intialized with
			// 	PyPreConfig_InitPythonConfig and PyConfig_InitPythonConfig
			// Otherwise, interpreter configuration is intialized with
			// 	PyPreConfig_InitIsolatedConfig and PyConfig_InitIsolatedConfig
			// https://docs.python.org/3/c-api/init_config.html#isolated-configuration
			int isolated = defaults::interpreter::isolated;

			// https://docs.python.org/3/c-api/init_config.html#c.PyPreConfig.dev_mode
			int dev_mode = defaults::interpreter::dev_mode;
			// https://docs.python.org/3/c-api/init_config.html#c.PyPreConfig.use_environment
			int use_environment = defaults::interpreter::use_environment;
			// https://docs.python.org/3/c-api/init_config.html#c.PyPreConfig.utf8_mode
			int utf8_mode = defaults::interpreter::utf8_mode;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.verbose
			int verbose = defaults::interpreter::verbose;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.hash_seed
			std::optional<unsigned long> hash_seed = defaults::interpreter::hash_seed;
#if PY_VERSION_HEX >= 0x030C0000
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.int_max_str_digits
			std::optional<int> int_max_str_digits = defaults::interpreter::int_max_str_digits;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.perf_profiling
			int perf_profiling = defaults::interpreter::perf_profiling;
#endif
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.xoptions
			std::optional<std::vector<std::wstring>> xoptions = defaults::interpreter::xoptions;

			// https://docs.python.org/3/c-api/init_config.html#c.PyPreConfig.configure_locale
			std::optional<int> configure_locale = defaults::interpreter::configure_locale;
			// https://docs.python.org/3/c-api/init_config.html#c.PyPreConfig.coerce_c_locale
			std::optional<int> coerce_c_locale = defaults::interpreter::coerce_c_locale;
			// https://docs.python.org/3/c-api/init_config.html#c.PyPreConfig.coerce_c_locale_warn
			std::optional<int> coerce_c_locale_warn = defaults::interpreter::coerce_c_locale_warn;

			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.site_import
			std::optional<int> site_import = defaults::interpreter::site_import;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.user_site_directory
			int user_site_directory = defaults::interpreter::user_site_directory;

			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.optimization_level
			std::optional<int> optimization_level = defaults::interpreter::optimization_level;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.write_bytecode
			std::optional<int> write_bytecode = defaults::interpreter::write_bytecode;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.pycache_prefix
			std::optional<std::wstring> pycache_prefix = defaults::interpreter::pycache_prefix;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.check_hash_pycs_mode
			std::wstring check_hash_pycs_mode = defaults::interpreter::check_hash_pycs_mode;

			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.base_prefix
			std::optional<std::wstring> base_prefix = defaults::interpreter::base_prefix;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.prefix
			std::optional<std::wstring> prefix = defaults::interpreter::prefix;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.base_exec_prefix
			std::optional<std::wstring> base_exec_prefix = defaults::interpreter::base_exec_prefix;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.exec_prefix
			std::optional<std::wstring> exec_prefix = defaults::interpreter::exec_prefix;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.base_executable
			std::optional<std::wstring> base_executable = defaults::interpreter::base_executable;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.executable
			std::optional<std::wstring> executable = defaults::interpreter::executable;

			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.filesystem_encoding
			std::optional<std::wstring> filesystem_encoding = defaults::interpreter::filesystem_encoding;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.filesystem_errors
			std::optional<std::wstring> filesystem_errors = defaults::interpreter::filesystem_errors;

			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.stdio_encoding
			std::optional<std::wstring> stdio_encoding = defaults::interpreter::stdio_encoding;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.stdio_errors
			std::optional<std::wstring> stdio_errors = defaults::interpreter::stdio_errors;

			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.buffered_stdio
			std::optional<int> buffered_stdio = defaults::interpreter::buffered_stdio;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.configure_c_stdio
			std::optional<int> configure_c_stdio = defaults::interpreter::configure_c_stdio;

			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.bytes_warning
			std::optional<int> bytes_warning = defaults::interpreter::bytes_warning;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.pathconfig_warnings
			std::optional<int> pathconfig_warnings = defaults::interpreter::pathconfig_warnings;
#if PY_VERSION_HEX >= 0x030A0000
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.warn_default_encoding
			std::optional<int> warn_default_encoding = defaults::interpreter::warn_default_encoding;
#endif
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.warnoptions
			std::optional<std::vector<std::wstring>> warnoptions = defaults::interpreter::warnoptions;

#ifdef Py_DEBUG
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.parser_debug
			int parser_debug = defaults::interpreter::parser_debug;
#endif
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.tracemalloc
			int tracemalloc = defaults::interpreter::tracemalloc;
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.import_time
			int import_time = defaults::interpreter::import_time;

			// Replaces the entire list of module search paths
			// https://docs.python.org/3/c-api/init_config.html#c.PyConfig.module_search_paths
			std::optional<std::vector<std::wstring>> module_search_paths = defaults::interpreter::module_search_paths;
#endif

			// alternative to module_search_paths; for prepending and appending to default module search path list
			// this is the only interpreter configuration supported for Python <3.8
			// if one is specified, both must be specified
			// cannot be specified with module_search_paths
			namespace additional_module_search_paths
			{
				std::optional<std::vector<pypath_string>> prepend = defaults::interpreter::additional_module_search_paths::prepend;
				std::optional<std::vector<pypath_string>> append = defaults::interpreter::additional_module_search_paths::append;
			} //namespace additional_module_search_paths
		} //namespace interpreter
	} // namespace plugin_configuration

	static BOOST_FORCEINLINE void set_default_interpreter_configs()
	{
#if PY_VERSION_HEX >= 0x03080000
			plugin_configuration::interpreter::isolated = plugin_configuration::defaults::interpreter::isolated;
			plugin_configuration::interpreter::dev_mode = plugin_configuration::defaults::interpreter::dev_mode;
			plugin_configuration::interpreter::use_environment = plugin_configuration::defaults::interpreter::use_environment;
			plugin_configuration::interpreter::utf8_mode = plugin_configuration::defaults::interpreter::utf8_mode;
			plugin_configuration::interpreter::verbose = plugin_configuration::defaults::interpreter::verbose;
			plugin_configuration::interpreter::hash_seed = plugin_configuration::defaults::interpreter::hash_seed;
#if PY_VERSION_HEX >= 0x030C0000
			plugin_configuration::interpreter::int_max_str_digits = plugin_configuration::defaults::interpreter::int_max_str_digits;
			plugin_configuration::interpreter::perf_profiling = plugin_configuration::defaults::interpreter::perf_profiling;
#endif
			plugin_configuration::interpreter::xoptions = plugin_configuration::defaults::interpreter::xoptions;
			plugin_configuration::interpreter::configure_locale = plugin_configuration::defaults::interpreter::configure_locale;
			plugin_configuration::interpreter::coerce_c_locale = plugin_configuration::defaults::interpreter::coerce_c_locale;
			plugin_configuration::interpreter::coerce_c_locale_warn = plugin_configuration::defaults::interpreter::coerce_c_locale_warn;
			plugin_configuration::interpreter::site_import = plugin_configuration::defaults::interpreter::site_import;
			plugin_configuration::interpreter::user_site_directory = plugin_configuration::defaults::interpreter::user_site_directory;
			plugin_configuration::interpreter::optimization_level = plugin_configuration::defaults::interpreter::optimization_level;
			plugin_configuration::interpreter::write_bytecode = plugin_configuration::defaults::interpreter::write_bytecode;
			plugin_configuration::interpreter::pycache_prefix = plugin_configuration::defaults::interpreter::pycache_prefix;
			plugin_configuration::interpreter::check_hash_pycs_mode = plugin_configuration::defaults::interpreter::check_hash_pycs_mode;
			plugin_configuration::interpreter::exec_prefix = plugin_configuration::defaults::interpreter::exec_prefix;
			plugin_configuration::interpreter::prefix = plugin_configuration::defaults::interpreter::prefix;
			plugin_configuration::interpreter::module_search_paths = plugin_configuration::defaults::interpreter::module_search_paths;
			plugin_configuration::interpreter::filesystem_encoding = plugin_configuration::defaults::interpreter::filesystem_encoding;
			plugin_configuration::interpreter::filesystem_errors = plugin_configuration::defaults::interpreter::filesystem_errors;
			plugin_configuration::interpreter::stdio_encoding = plugin_configuration::defaults::interpreter::stdio_encoding;
			plugin_configuration::interpreter::stdio_errors = plugin_configuration::defaults::interpreter::stdio_errors;
			plugin_configuration::interpreter::buffered_stdio = plugin_configuration::defaults::interpreter::buffered_stdio;
			plugin_configuration::interpreter::configure_c_stdio = plugin_configuration::defaults::interpreter::configure_c_stdio;
			plugin_configuration::interpreter::bytes_warning = plugin_configuration::defaults::interpreter::bytes_warning;
			plugin_configuration::interpreter::pathconfig_warnings = plugin_configuration::defaults::interpreter::pathconfig_warnings;
#if PY_VERSION_HEX >= 0x030A0000
			plugin_configuration::interpreter::warn_default_encoding = plugin_configuration::defaults::interpreter::warn_default_encoding;
#endif
			plugin_configuration::interpreter::warnoptions = plugin_configuration::defaults::interpreter::warnoptions;
#ifdef Py_DEBUG
			plugin_configuration::interpreter::parser_debug = plugin_configuration::defaults::interpreter::parser_debug;
#endif
			plugin_configuration::interpreter::tracemalloc = plugin_configuration::defaults::interpreter::tracemalloc;
			plugin_configuration::interpreter::import_time = plugin_configuration::defaults::interpreter::import_time;
#endif
			plugin_configuration::interpreter::additional_module_search_paths::prepend = plugin_configuration::defaults::interpreter::additional_module_search_paths::prepend;
			plugin_configuration::interpreter::additional_module_search_paths::append = plugin_configuration::defaults::interpreter::additional_module_search_paths::append;
	}

	static BOOST_FORCEINLINE irods::error get_re_configs(const std::string& _instance_name)
	{
		try {
			const auto& re_plugin_arr = irods::get_server_property<const nlohmann::json&>(
				std::vector<std::string>{irods::KW_CFG_PLUGIN_CONFIGURATION, irods::KW_CFG_PLUGIN_TYPE_RULE_ENGINE});
			for (const auto& plugin_config : re_plugin_arr) {
				const auto& inst_name = plugin_config.at(irods::KW_CFG_INSTANCE_NAME).get_ref<const std::string&>();
				if (inst_name != _instance_name) {
					continue;
				}

				const auto& plugin_spec_cfg = plugin_config.at(irods::KW_CFG_PLUGIN_SPECIFIC_CONFIGURATION);

				// TODO(#226): Enable non core.py Python rulebases

				re_pep_regex_set_iter = plugin_spec_cfg.find(irods::KW_CFG_RE_PEP_REGEX_SET);
				if (re_pep_regex_set_iter == plugin_spec_cfg.end()) {
					plugin_configuration::re_pep_regex_set = plugin_configuration::defaults::re_pep_regex_set;
					// clang-format off
					log_re::debug({
						{"rule_engine_plugin", rule_engine_name},
						{"instance_name", _instance_name},
						{"log_message", "No regexes found in server_config for Python RE - using default regexes"}
					});
					// clang-format on
				}
				else {
					const auto& re_pep_regex_set_cfg = re_pep_regex_set_iter.get_ref<const nlohmann::json&>();
					plugin_configuration::re_pep_regex_set.clear();
					for (const auto& re_pep_regex_cfg : re_pep_regex_set_cfg) {
						const auto& re_pep_regex = re_pep_regex_cfg.get_ref<const std::string&>();
						plugin_configuration::re_pep_regex_set.push_back(re_pep_regex);
						// clang-format off
						log_re::debug({
							{"rule_engine_plugin", rule_engine_name},
							{"instance_name", _instance_name},
							{"regex", re_pep_regex},
						});
						// clang-format on
					}
				}

				const auto interpreter_iter = plugin_spec_cfg.find("interpreter");
				if (interpreter_iter == plugin_spec_cfg.end()) {
					set_default_interpreter_configs();
					log_re::debug({
						{"rule_engine_plugin", rule_engine_name},
						{"instance_name", _instance_name},
						{"message", "using default interpreter configuration"},
					});
				}
				else {
					const auto& interpreter_cfg = interpreter_iter.get_ref<const nlohmann::json&>();

					const auto additional_module_search_paths_iter = interpreter_cfg.find("additional_module_search_paths");
					if (additional_module_search_paths_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::additional_module_search_paths::prepend = plugin_configuration::defaults::interpreter::additional_module_search_paths::prepend;
						plugin_configuration::interpreter::additional_module_search_paths::append = plugin_configuration::defaults::interpreter::additional_module_search_paths::append;
					}
					else {
						const auto& additional_module_search_paths_cfg = additional_module_search_paths_iter.get_ref<const nlohmann::json&>();

						const auto prepend_paths_iter = additional_module_search_paths_cfg.find("prepend");
						if (prepend_paths_iter == additional_module_search_paths_cfg.end()) {
							plugin_configuration::interpreter::additional_module_search_paths::prepend = plugin_configuration::defaults::interpreter::additional_module_search_paths::prepend;
						}
						else {
							const auto& prepend_paths_cfg = prepend_paths_iter.get_ref<const nlohmann::json&>();
							std::vector<std::wstring> prepend;
							for (const auto& prepend_path_iter : prepend_paths_cfg) {
								const auto& prepend_path = prepend_path_iter.get_ref<const std::string&>();
								prepend.push_back(get_pypath_string(prepend_path));
							}
							plugin_configuration::interpreter::additional_module_search_paths::prepend = prepend;
						}
						
						const auto append_paths_iter = additional_module_search_paths_cfg.find("append");
						if (append_paths_iter == additional_module_search_paths_cfg.end()) {
							plugin_configuration::interpreter::additional_module_search_paths::append = plugin_configuration::defaults::interpreter::additional_module_search_paths::append;
						}
						else {
							const auto& append_paths_cfg = append_paths_iter.get_ref<const nlohmann::json&>();
							std::vector<std::wstring> append;
							for (const auto& append_path_iter : append_paths_cfg) {
								const auto& append_path = append_path_iter.get_ref<const std::string&>();
								append.push_back(get_pypath_string(append_path));
							}
							plugin_configuration::interpreter::additional_module_search_paths::append = append;
						}
					}

					if (plugin_configuration::interpreter::additional_module_search_paths::prepend.has_value() !=
						plugin_configuration::interpreter::additional_module_search_paths::append.has_value()) {
						// clang-format off
						log_re::error({
							{"rule_engine_plugin", rule_engine_name},
							{"instance_name", _instance_name},
							{"message", "Configuration error: only one of additional_module_search_paths defined"},
						});
						// clang-format on
						auto msg = fmt::format("only one of additional_module_search_paths defined for re-python plugin [{}]", _instance_name);
						return ERROR(SYS_INVALID_INPUT_PARAM, msg);
					}

#if PY_VERSION_HEX < 0x03080000
					// clang-format off
					log_re::warning({
						{"rule_engine_plugin", rule_engine_name},
						{"instance_name", _instance_name},
						{"message", "interpreter configuration found, but Python version does not support PyConfig; most interpreter configuration options will be ignored"},
					});
					// clang-format on
#else

					const auto isolated_iter = interpreter_cfg.find("isolated");
					if (isolated_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::isolated = plugin_configuration::defaults::interpreter::isolated;
					}
					else {
						plugin_configuration::interpreter::isolated = isolated_iter.get<int>();
					}

					const auto dev_mode_iter = interpreter_cfg.find("dev_mode");
					if (dev_mode_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::dev_mode = plugin_configuration::defaults::interpreter::dev_mode;
					}
					else {
						plugin_configuration::interpreter::dev_mode = dev_mode_iter.get<int>();
					}

					const auto use_environment_iter = interpreter_cfg.find("use_environment");
					if (use_environment_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::use_environment = plugin_configuration::defaults::interpreter::use_environment;
					}
					else {
						plugin_configuration::interpreter::use_environment = use_environment_iter.get<int>();
					}

					const auto utf8_mode_iter = interpreter_cfg.find("utf8_mode");
					if (utf8_mode_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::utf8_mode = plugin_configuration::defaults::interpreter::utf8_mode;
					}
					else {
						plugin_configuration::interpreter::utf8_mode = utf8_mode_iter.get<int>();
					}

					const auto verbose_iter = interpreter_cfg.find("verbose");
					if (verbose_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::verbose = plugin_configuration::defaults::interpreter::verbose;
					}
					else {
						plugin_configuration::interpreter::verbose = verbose_iter.get<int>();
					}

					const auto hash_seed_iter = interpreter_cfg.find("hash_seed");
					if (hash_seed_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::hash_seed = plugin_configuration::defaults::interpreter::hash_seed;
					}
					else {
						plugin_configuration::interpreter::hash_seed = hash_seed_iter.get<unsigned long>();
					}

#if PY_VERSION_HEX >= 0x030C0000
					const auto int_max_str_digits_iter = interpreter_cfg.find("int_max_str_digits");
					if (int_max_str_digits_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::int_max_str_digits = plugin_configuration::defaults::interpreter::int_max_str_digits;
					}
					else {
						plugin_configuration::interpreter::int_max_str_digits = int_max_str_digits_iter.get<int>();
					}

					const auto perf_profiling_iter = interpreter_cfg.find("perf_profiling");
					if (perf_profiling_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::perf_profiling = plugin_configuration::defaults::interpreter::perf_profiling;
					}
					else {
						plugin_configuration::interpreter::perf_profiling = perf_profiling_iter.get<int>();
					}
#endif

					const auto xoptions_iter = interpreter_cfg.find("xoptions");
					if (xoptions_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::xoptions = plugin_configuration::defaults::interpreter::xoptions;
					}
					else {
						const auto& xoptions_cfg = xoptions_iter.get_ref<const nlohmann::json&>();
						std::vector<std::wstring> xoptions;
						for (const auto& xoption_iter : xoptions_cfg) {
							const auto& xoption = xoption_iter.get_ref<const std::string&>();
							xoptions.push_back(wstring_converter.from_bytes(xoption));
						}
						plugin_configuration::interpreter::xoptions = xoptions;
					}

					const auto configure_locale_iter = interpreter_cfg.find("configure_locale");
					if (configure_locale_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::configure_locale = plugin_configuration::defaults::interpreter::configure_locale;
					}
					else {
						plugin_configuration::interpreter::configure_locale = configure_locale_iter.get<int>();
					}

					const auto coerce_c_locale_iter = interpreter_cfg.find("coerce_c_locale");
					if (coerce_c_locale_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::coerce_c_locale = plugin_configuration::defaults::interpreter::coerce_c_locale;
					}
					else {
						plugin_configuration::interpreter::coerce_c_locale = coerce_c_locale_iter.get<int>();
					}

					const auto coerce_c_locale_warn_iter = interpreter_cfg.find("coerce_c_locale_warn");
					if (coerce_c_locale_warn_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::coerce_c_locale_warn = plugin_configuration::defaults::interpreter::coerce_c_locale_warn;
					}
					else {
						plugin_configuration::interpreter::coerce_c_locale_warn = coerce_c_locale_warn_iter.get<int>();
					}

					const auto site_import_iter = interpreter_cfg.find("site_import");
					if (site_import_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::site_import = plugin_configuration::defaults::interpreter::site_import;
					}
					else {
						plugin_configuration::interpreter::site_import = site_import_iter.get<int>();
					}

					const auto user_site_directory_iter = interpreter_cfg.find("user_site_directory");
					if (user_site_directory_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::user_site_directory = plugin_configuration::defaults::interpreter::user_site_directory;
					}
					else {
						plugin_configuration::interpreter::user_site_directory = user_site_directory_iter.get<int>();
					}

					const auto optimization_level_iter = interpreter_cfg.find("optimization_level");
					if (optimization_level_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::optimization_level = plugin_configuration::defaults::interpreter::optimization_level;
					}
					else {
						plugin_configuration::interpreter::optimization_level = optimization_level_iter.get<int>();
					}

					const auto write_bytecode_iter = interpreter_cfg.find("write_bytecode");
					if (write_bytecode_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::write_bytecode = plugin_configuration::defaults::interpreter::write_bytecode;
					}
					else {
						plugin_configuration::interpreter::write_bytecode = write_bytecode_iter.get<int>();
					}

					const auto pycache_prefix_iter = interpreter_cfg.find("pycache_prefix");
					if (pycache_prefix_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::pycache_prefix = plugin_configuration::defaults::interpreter::pycache_prefix;
					}
					else {
						const auto& pycache_prefix = pycache_prefix_iter.get_ref<const std::string&>();
						plugin_configuration::interpreter::pycache_prefix = get_pypath_string(pycache_prefix);
					}

					const auto check_hash_pycs_mode_iter = interpreter_cfg.find("check_hash_pycs_mode");
					if (check_hash_pycs_mode_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::check_hash_pycs_mode = plugin_configuration::defaults::interpreter::check_hash_pycs_mode;
					}
					else {
						const auto& check_hash_pycs_mode = check_hash_pycs_mode_iter.get_ref<const std::string&>();
						plugin_configuration::interpreter::check_hash_pycs_mode = wstring_converter.from_bytes(check_hash_pycs_mode);
					}

					const auto exec_prefix_iter = interpreter_cfg.find("exec_prefix");
					if (exec_prefix_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::exec_prefix = plugin_configuration::defaults::interpreter::exec_prefix;
					}
					else {
						const auto& exec_prefix = exec_prefix_iter.get_ref<const std::string&>();
						plugin_configuration::interpreter::exec_prefix = get_pypath_string(exec_prefix);
					}

					const auto prefix_iter = interpreter_cfg.find("prefix");
					if (prefix_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::prefix = plugin_configuration::defaults::interpreter::prefix;
					}
					else {
						const auto& prefix = prefix_iter.get_ref<const std::string&>();
						plugin_configuration::interpreter::prefix = get_pypath_string(prefix);
					}

					const auto filesystem_encoding_iter = interpreter_cfg.find("filesystem_encoding");
					if (filesystem_encoding_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::filesystem_encoding = plugin_configuration::defaults::interpreter::filesystem_encoding;
					}
					else {
						const auto& filesystem_encoding = filesystem_encoding_iter.get_ref<const std::string&>();
						plugin_configuration::interpreter::filesystem_encoding = wstring_converter.from_bytes(filesystem_encoding);
					}

					const auto filesystem_errors_iter = interpreter_cfg.find("filesystem_errors");
					if (filesystem_errors_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::filesystem_errors = plugin_configuration::defaults::interpreter::filesystem_errors;
					}
					else {
						const auto& filesystem_errors = filesystem_errors_iter.get_ref<const std::string&>();
						plugin_configuration::interpreter::filesystem_errors = wstring_converter.from_bytes(filesystem_errors);
					}

					const auto stdio_encoding_iter = interpreter_cfg.find("stdio_encoding");
					if (stdio_encoding_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::stdio_encoding = plugin_configuration::defaults::interpreter::stdio_encoding;
					}
					else {
						const auto& stdio_encoding = stdio_encoding_iter.get_ref<const std::string&>();
						plugin_configuration::interpreter::stdio_encoding = wstring_converter.from_bytes(stdio_encoding);
					}

					const auto stdio_errors_iter = interpreter_cfg.find("stdio_errors");
					if (stdio_errors_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::stdio_errors = plugin_configuration::defaults::interpreter::stdio_errors;
					}
					else {
						const auto& stdio_errors = stdio_errors_iter.get_ref<const std::string&>();
						plugin_configuration::interpreter::stdio_errors = wstring_converter.from_bytes(stdio_errors);
					}

					const auto buffered_stdio_iter = interpreter_cfg.find("buffered_stdio");
					if (buffered_stdio_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::buffered_stdio = plugin_configuration::defaults::interpreter::buffered_stdio;
					}
					else {
						plugin_configuration::interpreter::buffered_stdio = buffered_stdio_iter.get<int>();
					}

					const auto configure_c_stdio_iter = interpreter_cfg.find("configure_c_stdio");
					if (configure_c_stdio_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::configure_c_stdio = plugin_configuration::defaults::interpreter::configure_c_stdio;
					}
					else {
						plugin_configuration::interpreter::configure_c_stdio = configure_c_stdio_iter.get<int>();
					}

					const auto bytes_warning_iter = interpreter_cfg.find("bytes_warning");
					if (bytes_warning_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::bytes_warning = plugin_configuration::defaults::interpreter::bytes_warning;
					}
					else {
						plugin_configuration::interpreter::bytes_warning = bytes_warning_iter.get<int>();
					}

					const auto pathconfig_warnings_iter = interpreter_cfg.find("pathconfig_warnings");
					if (pathconfig_warnings_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::pathconfig_warnings = plugin_configuration::defaults::interpreter::pathconfig_warnings;
					}
					else {
						plugin_configuration::interpreter::pathconfig_warnings = pathconfig_warnings_iter.get<int>();
					}

#if PY_VERSION_HEX >= 0x030A0000
					const auto warn_default_encoding_iter = interpreter_cfg.find("warn_default_encoding");
					if (warn_default_encoding_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::warn_default_encoding = plugin_configuration::defaults::interpreter::warn_default_encoding;
					}
					else {
						plugin_configuration::interpreter::warn_default_encoding = warn_default_encoding_iter.get<int>();
					}
#endif

					const auto warnoptions_iter = interpreter_cfg.find("warnoptions");
					if (warnoptions_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::warnoptions = plugin_configuration::defaults::interpreter::warnoptions;
					}
					else {
						const auto& warnoptions_cfg = warnoptions_iter.get_ref<const nlohmann::json&>();
						std::vector<std::wstring> warnoptions;
						for (const auto& warnoption_iter : warnoptions_cfg) {
							const auto& warnoption = warnoption_iter.get_ref<const std::string&>();
							warnoptions.push_back(wstring_converter.from_bytes(warnoption));
						}
						plugin_configuration::interpreter::warnoptions = warnoptions;
					}

#ifdef Py_DEBUG
					const auto parser_debug_iter = interpreter_cfg.find("parser_debug");
					if (parser_debug_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::parser_debug = plugin_configuration::defaults::interpreter::parser_debug;
					}
					else {
						plugin_configuration::interpreter::parser_debug = parser_debug_iter.get<int>();
					}
#endif

					const auto tracemalloc_iter = interpreter_cfg.find("tracemalloc");
					if (tracemalloc_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::tracemalloc = plugin_configuration::defaults::interpreter::tracemalloc;
					}
					else {
						plugin_configuration::interpreter::tracemalloc = tracemalloc_iter.get<int>();
					}

					const auto import_time_iter = interpreter_cfg.find("import_time");
					if (import_time_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::import_time = plugin_configuration::defaults::interpreter::import_time;
					}
					else {
						plugin_configuration::interpreter::import_time = import_time_iter.get<int>();
					}

					const auto module_search_paths_iter = interpreter_cfg.find("module_search_paths");
					if (module_search_paths_iter == interpreter_cfg.end()) {
						plugin_configuration::interpreter::module_search_paths = plugin_configuration::defaults::interpreter::module_search_paths;
					}
					else {
						const auto& module_search_paths_cfg = module_search_paths_iter.get_ref<const nlohmann::json&>();
						std::vector<std::wstring> module_search_paths;
						for (const auto& module_search_path_iter : module_search_paths_cfg) {
							const auto& module_search_path = module_search_path_iter.get_ref<const std::string&>();
							module_search_paths.push_back(get_pypath_string(module_search_path));
						}
						plugin_configuration::interpreter::module_search_paths = module_search_paths;
					}

					if (plugin_configuration::interpreter::module_search_paths.has_value()) {
						if (plugin_configuration::interpreter::additional_module_search_paths::prepend.has_value() ||
							plugin_configuration::interpreter::additional_module_search_paths::append.has_value()) {
							// clang-format off
							log_re::error({
								{"rule_engine_plugin", rule_engine_name},
								{"instance_name", _instance_name},
								{"message", "Configuration error: both module_search_paths and additional_module_search_paths defined"},
							});
							// clang-format on
							auto msg = fmt::format("both module_search_paths and additional_module_search_paths defined for re-python plugin [{}]", _instance_name);
							return ERROR(SYS_INVALID_INPUT_PARAM, msg);
						}
					}
#endif
				}
				return SUCCESS();
			}
		}
		catch (const irods::exception& e) {
			return irods::error(e);
		}
		catch (const boost::bad_any_cast& e) {
			return ERROR(INVALID_ANY_CAST, e.what());
		}
		catch (const std::out_of_range& e) {
			return ERROR(KEY_NOT_FOUND, e.what());
		}
		catch (const nlohmann::json::exception& e) {
			return ERROR(SYS_LIBRARY_ERROR, e.what());
		}
		catch (const std::exception& e) {
			return ERROR(SYS_INTERNAL_ERR, e.what());
		}
		catch (...) {
			return ERROR(SYS_UNKNOWN_ERROR, "an unknown error occurred");
		}

		// clang-format off
		log_re::error({
			{"rule_engine_plugin", rule_engine_name},
			{"instance_name", _instance_name},
			{"log_message", "failed to find configuration for plugin"},
		});
		// clang-format on
		auto msg = fmt::format("failed to find configuration for re-python plugin [{}]", _instance_name);
		return ERROR(SYS_INVALID_INPUT_PARAM, msg);

	}

	irods::error to_irods_error_object(const bp::object& object)
	{
		if (bp::extract<int> result{object}; result.check()) {
			const int ec = result();

			if (ec < 0) {
				return ERROR(ec, "");
			}

			return CODE(ec);
		}

		return SUCCESS();
	}

	std::string extract_python_exception(void)
	{
		PyObject *exc, *val, *tb;
		PyErr_Fetch(&exc, &val, &tb);
		PyErr_NormalizeException(&exc, &val, &tb);
		bp::handle<> hexc(exc), hval(bp::allow_null(val)), htb(bp::allow_null(tb));

		if (!hval) {
			return bp::extract<std::string>(bp::str(hexc));
		}
		else {
			bp::object traceback(bp::import("traceback"));
			bp::object format_exception(traceback.attr("format_exception"));
			bp::object formatted_list(format_exception(hexc, hval, htb));
			bp::object formatted(bp::str("").join(formatted_list));

			return bp::extract<std::string>(formatted);
		}
	}

	namespace StringFromPythonUnicode
	{
		void* convertible(PyObject* py_obj)
		{
			if (PyUnicode_Check(py_obj)) {
				return py_obj;
			}

			return nullptr;
		}

		void construct(PyObject* py_obj, boost::python::converter::rvalue_from_python_stage1_data* data)
		{
			bp::handle<> h_encoded(PyUnicode_AsUTF8String(py_obj));
			void* storage = reinterpret_cast<boost::python::converter::rvalue_from_python_storage<std::string>*>(data)
			                    ->storage.bytes;
			new (storage) std::string(PyBytes_AsString(h_encoded.get()));
			data->convertible = storage;
		}

		void register_converter()
		{
			bp::converter::registry::push_back(&convertible, &construct, bp::type_id<std::string>());
		}
	} // namespace StringFromPythonUnicode

	ruleExecInfo_t* get_rei_from_effect_handler(irods::callback effect_handler)
	{
		ruleExecInfo_t* rei = nullptr;
		irods::error err = effect_handler("unsafe_ms_ctx", &rei);

		if (!err.ok()) {
			// clang-format off
			log_re::error({
				{"rule_engine_plugin", rule_engine_name},
				{"log_message", "Could not retrieve RuleExecInfo_t object from effect handler"},
			});
			// clang-format on
			return nullptr;
		}

		if (!rei) {
			// clang-format off
			log_re::error({
				{"rule_engine_plugin", rule_engine_name},
				{"log_message", "RuleExecInfo object is NULL - cannot populate session vars"},
			});
			// clang-format on
			return nullptr;
		}

		return rei;
	}

	// Helper class that acquires the GIL while in scope
	class python_gil_lock
	{
	public:
		python_gil_lock()
			: _previous_gil_state(PyGILState_Ensure())
		{ }

		~python_gil_lock()
		{
			if (!_released) {
				PyGILState_Release(_previous_gil_state);
			}
		}

		python_gil_lock(const python_gil_lock&) = delete;

		python_gil_lock& operator=(const python_gil_lock&) = delete;

		BOOST_FORCEINLINE bool released()
		{
			return _released;
		}

		// restores python state to prior to last PyGILState_Ensure call
		// returns active PyThreadState
		// doesn't necessarily release the GIL, only this instance's hold on it.
		// if GIL was acquired further up the stack, it will still be locked. 
		BOOST_FORCEINLINE PyThreadState* release()
		{
			if (_released) {
				THROW(RULE_ENGINE_ERROR, "release called on already-released python_gil_lock");
			}

			PyThreadState* current_thread_state = PyThreadState_Get();
			if (current_thread_state->gilstate_counter <= 1) {
				current_thread_state = nullptr;
			}

			PyGILState_Release(_previous_gil_state);

			_released = true;
			return current_thread_state;
		}

		// reacquires GIL after a call to release
		BOOST_FORCEINLINE void reacquire()
		{
			if (_released) {
				THROW(RULE_ENGINE_ERROR, "reacquire called on non-released python_gil_lock");
			}

			_previous_gil_state = PyGILState_Ensure();
			_released = false;
		}

	private:
		PyGILState_STATE _previous_gil_state; // GIL state prior to calling PyGILState_Ensure
		bool _released = false; // whether or not PyGILState_Release has already been called

	}; //class python_gil_lock

	// Helper class that unlocks GIL while in scope
	class python_gil_unlock
	{
	public:
		// Saves the current thread state, releasing the GIL
		// Does not otherwise alter thread state in any way
		python_gil_unlock()
			: _previous_thread_state(PyEval_SaveThread())
		{ }

		// Calls release on gil_lock and, if necessary, saves the current thread state
		// if should_reacquire is true, reacquire is called on gil_lock during destruction
		python_gil_unlock(python_gil_lock* const gil_lock, bool should_reacquire)
			: _gil_lock(gil_lock), _should_reacquire(should_reacquire)
		{
			if (_gil_lock->release() != nullptr) {
				_previous_thread_state = PyEval_SaveThread();
			}
		}

		~python_gil_unlock()
		{
			if (_previous_thread_state != nullptr) {
				PyEval_RestoreThread(_previous_thread_state);
			}
			if (_should_reacquire) {
				assert(_gil_lock != nullptr);
				_gil_lock->reacquire();
			}
		}

		python_gil_unlock(const python_gil_unlock&) = delete;

		python_gil_unlock& operator=(const python_gil_unlock&) = delete;

	private:
		PyThreadState* _previous_thread_state = nullptr;
		python_gil_lock* const _gil_lock = nullptr;
		const bool _should_reacquire = false;

	}; //class python_gil_unlock

	struct RuleCallWrapper
	{
		RuleCallWrapper(irods::callback& effect_handler, std::string rule_name)
			: effect_handler{effect_handler}
			, rule_name{rule_name}
		{
		}

		irods::callback& effect_handler;
		std::string rule_name;

		static bp::dict call(const bp::tuple& args, const bp::dict&)
		{
			RuleCallWrapper& self = bp::extract<RuleCallWrapper&>(args[0]);

			bp::tuple rule_args_python = bp::extract<bp::tuple>(args[bp::slice(1, bp::len(args))]);
			std::list<boost::any> rule_args_cpp;
			std::list<msParam_t> msParams;
			std::list<std::string> strings;

			for (auto&& rule_arg_python : rule_args_python) {
				bp::extract<std::string> s{rule_arg_python};
				if (s.check()) {
					strings.push_back(s());
					rule_args_cpp.emplace_back(&strings.back());
				}
				else {
					msParams.push_back(msParam_from_object<genQueryInp_t,
					                                       genQueryOut_t,
					                                       keyValPair_t,
					                                       fileLseekOut_t,
					                                       rodsObjStat_t,
					                                       bytesBuf_t,
					                                       int,
					                                       float>(rule_arg_python));
					rule_args_cpp.emplace_back(&msParams.back());
				}
			}

			const auto err = self.effect_handler(self.rule_name, irods::unpack(rule_args_cpp));

			const auto error_occurred =
				!err.ok() && err.code() != CAT_NO_ROWS_FOUND && err.code() != CAT_SUCCESS_BUT_WITH_NO_INFO;

			bp::list ret_list{};
			while (!rule_args_cpp.empty()) {
				auto& rule_arg_cpp = rule_args_cpp.front();

				if (rule_arg_cpp.type() == typeid(std::string*)) {
					ret_list.append(strings.front());
					strings.pop_front();
				}
				else {
					ret_list.append(object_from_msParam(msParams.front()));

					if (!error_occurred) {
						clearMsParam(&msParams.front(), 1);
					}

					msParams.pop_front();
				}

				rule_args_cpp.pop_front();
			}

			if (error_occurred) {
				std::string returnString =
					IRODS_ERROR_PREFIX + boost::lexical_cast<std::string>(err.code()) + "] " + err.result().c_str();
				PyErr_SetString(PyExc_RuntimeError, returnString.c_str());
				bp::throw_error_already_set();
			}

			bp::dict ret;
			ret["code"] = err.code();
			ret["status"] = err.status();
			ret["arguments"] = ret_list;
			return ret;
		}
	}; // struct RuleCallWrapper

	struct CallbackWrapper
	{
		CallbackWrapper(irods::callback& effect_handler)
			: effect_handler{effect_handler}
		{
		}

		irods::callback& effect_handler;

		RuleCallWrapper getAttribute(const std::string& rule_name)
		{
			return RuleCallWrapper{effect_handler, rule_name};
		}
	}; // struct CallbackWrapper

	BOOST_PYTHON_MODULE(plugin_wrappers)
	{
		bp::class_<RuleCallWrapper>("RuleCallWrapper", bp::no_init)
			.def("__call__", bp::raw_function(&RuleCallWrapper::call, 1));

		bp::class_<CallbackWrapper>("CallbackWrapper", bp::no_init)
			.def("__getattribute__", &CallbackWrapper::getAttribute);
	}

#if PY_VERSION_HEX >= 0x03080000
	static BOOST_FORCEINLINE void populate_PyPreConfig(PyPreConfig& py_preconfig, bool early)
	{
		if (0 < plugin_configuration::interpreter::isolated) {
			PyPreConfig_InitIsolatedConfig(&py_preconfig);
		}
		else {
			PyPreConfig_InitPythonConfig(&py_preconfig);
		}

		py_preconfig.isolated = plugin_configuration::interpreter::isolated;
		py_preconfig.use_environment = plugin_configuration::interpreter::use_environment;

		if (early) {
			// don't use user config for these during early preconfig
			py_preconfig.dev_mode = plugin_configuration::interpreter::defaults::dev_mode;
			py_preconfig.utf8_mode = plugin_configuration::interpreter::defaults::utf8_mode;
		}
		else {
			py_preconfig.dev_mode = plugin_configuration::interpreter::dev_mode;
			py_preconfig.utf8_mode = plugin_configuration::interpreter::utf8_mode;
		}

		if (plugin_configuration::interpreter::configure_locale.has_value()) {
			py_preconfig.configure_locale = plugin_configuration::interpreter::configure_locale.value();
		}
		if (plugin_configuration::interpreter::coerce_c_locale.has_value()) {
			py_preconfig.coerce_c_locale = plugin_configuration::interpreter::coerce_c_locale.value();
		}
		if (plugin_configuration::interpreter::coerce_c_locale_warn.has_value()) {
			py_preconfig.coerce_c_locale_warn = plugin_configuration::interpreter::coerce_c_locale_warn.value();
		}

	}

	static BOOST_FORCEINLINE void populate_PyConfig(PyConfig& py_config, bool early)
	{
		if (0 < plugin_configuration::interpreter::isolated) {
			PyConfig_InitIsolatedConfig(&py_config);
		}
		else {
			PyConfig_InitPythonConfig(&py_config);
		}

		py_config.parse_argv = 0;
#if PY_VERSION_HEX >= 0x030B0000
		py_config.safe_path = -1;
#endif

		py_config.isolated = plugin_configuration::interpreter::isolated;
		py_config.use_environment = plugin_configuration::interpreter::use_environment;

		if (early) {
			// don't use user config for these during early preconfig
			py_config.dev_mode = plugin_configuration::interpreter::defaults::dev_mode;
			py_config.verbose = plugin_configuration::interpreter::defaults::verbose;
#ifdef Py_DEBUG
			py_config.parser_debug = plugin_configuration::interpreter::defaults::parser_debug;
#endif
			py_config.tracemalloc = plugin_configuration::interpreter::defaults::tracemalloc;
			py_config.import_time = plugin_configuration::interpreter::defaults::import_time;
		}
		else {
			py_config.dev_mode = plugin_configuration::interpreter::dev_mode;
			py_config.verbose = plugin_configuration::interpreter::verbose;
#ifdef Py_DEBUG
			py_config.parser_debug = plugin_configuration::interpreter::parser_debug;
#endif
			py_config.tracemalloc = plugin_configuration::interpreter::tracemalloc;
			py_config.import_time = plugin_configuration::interpreter::import_time;
		}

		if (plugin_configuration::interpreter::hash_seed.has_value()) {
			py_config.hash_seed = plugin_configuration::interpreter::hash_seed.value();
		}
#if PY_VERSION_HEX >= 0x030C0000
		if (plugin_configuration::interpreter::int_max_str_digits.has_value()) {
			py_config.int_max_str_digits = plugin_configuration::interpreter::int_max_str_digits.value();
		}
		py_config.perf_profiling = plugin_configuration::interpreter::perf_profiling;
#endif

		if (plugin_configuration::interpreter::xoptions.has_value()) {
			for (const auto&& xoption : plugin_configuration::interpreter::xoptions.value()) {
				PyWideStringList_Append(&py_config.xoptions, xoption.c_str());
			}
		}

		if (plugin_configuration::interpreter::site_import.has_value()) {
			py_config.site_import = plugin_configuration::interpreter::site_import.value();
		}
		py_config.user_site_directory = plugin_configuration::interpreter::user_site_directory;

		if (plugin_configuration::interpreter::optimization_level.has_value()) {
			py_config.optimization_level = plugin_configuration::interpreter::optimization_level.value();
		}
		if (plugin_configuration::interpreter::write_bytecode.has_value()) {
			py_config.write_bytecode = plugin_configuration::interpreter::write_bytecode.value();
		}
		if (plugin_configuration::interpreter::pycache_prefix.has_value()) {
			PyConfig_SetString(&config, &config.pycache_prefix, plugin_configuration::interpreter::pycache_prefix.value().c_str());
		}
		if (plugin_configuration::interpreter::check_hash_pycs_mode.has_value()) {
			PyConfig_SetString(&config, &config.check_hash_pycs_mode, plugin_configuration::interpreter::check_hash_pycs_mode.value().c_str());
		}

		if (plugin_configuration::interpreter::exec_prefix.has_value()) {
			PyConfig_SetString(&config, &config.exec_prefix, plugin_configuration::interpreter::exec_prefix.value().c_str());
		}
		if (plugin_configuration::interpreter::prefix.has_value()) {
			PyConfig_SetString(&config, &config.prefix, plugin_configuration::interpreter::prefix.value().c_str());
		}

		if (plugin_configuration::interpreter::filesystem_encoding.has_value()) {
			PyConfig_SetString(&config, &config.filesystem_encoding, plugin_configuration::interpreter::filesystem_encoding.value().c_str());
		}
		if (plugin_configuration::interpreter::filesystem_errors.has_value()) {
			PyConfig_SetString(&config, &config.filesystem_errors, plugin_configuration::interpreter::filesystem_errors.value().c_str());
		}

		if (plugin_configuration::interpreter::stdio_encoding.has_value()) {
			PyConfig_SetString(&config, &config.stdio_encoding, plugin_configuration::interpreter::stdio_encoding.value().c_str());
		}
		if (plugin_configuration::interpreter::stdio_errors.has_value()) {
			PyConfig_SetString(&config, &config.stdio_errors, plugin_configuration::interpreter::stdio_errors.value().c_str());
		}

		if (plugin_configuration::interpreter::buffered_stdio.has_value()) {
			py_config.buffered_stdio = plugin_configuration::interpreter::buffered_stdio.value();
		}
		if (plugin_configuration::interpreter::configure_c_stdio.has_value()) {
			py_config.configure_c_stdio = plugin_configuration::interpreter::configure_c_stdio.value();
		}

		if (plugin_configuration::interpreter::bytes_warning.has_value()) {
			py_config.bytes_warning = plugin_configuration::interpreter::bytes_warning.value();
		}
		if (plugin_configuration::interpreter::pathconfig_warnings.has_value()) {
			py_config.pathconfig_warnings = plugin_configuration::interpreter::pathconfig_warnings.value();
		}
#if PY_VERSION_HEX >= 0x030A0000
		if (plugin_configuration::interpreter::warn_default_encoding.has_value()) {
			py_config.warn_default_encoding = plugin_configuration::interpreter::warn_default_encoding.value();
		}
#endif
		if (plugin_configuration::interpreter::warnoptions.has_value()) {
			for (const auto&& warnoption : plugin_configuration::interpreter::warnoptions.value()) {
				PyWideStringList_Append(&py_config.warnoptions, warnoption.c_str());
			}
		}

	}
#endif

	static BOOST_FORCEINLINE void initialize_python(const std::string& _instance_name)
	{
#if PY_VERSION_HEX >= 0x03080000
		PyConfig py_config;
		PyStatus py_status;

		if (!plugin_configuration::interpreter::module_search_paths.has_value()) {
			// module_search_paths not set - need to pull default paths
			PyPreConfig py_preconfig_early;
			populate_PyPreConfig(py_preconfig_early, true);
			py_status = Py_PreInitialize(&py_preconfig_early);

			if (PyStatus_Exception(py_status)) {
				// clang-format off
				log_re::error({
					{"rule_engine_plugin", rule_engine_name},
					{"instance_name", _instance_name},
					{"log_message", "Failed early preinitialization of interpreter"},
					{"PyStatus.exitcode", fmt::to_string(py_status.exitcode)},
					{"PyStatus.err_msg", py_status.err_msg},
					{"PyStatus.func", py_status.func},
				});
				// clang-format on
				auto msg = fmt::format("failed early preinitialization of interpreter for re-python plugin [{}]", _instance_name);
				return ERROR(SYS_LIBRARY_ERROR, msg);
			}

			populate_PyPreConfig(py_config, true);
		}

#if PY_VERSION_HEX >= 0x03080000
		if (python_state::default_module_search_paths_set) {
			PyConfig py_config;
			PyConfig_InitPythonConfig(&py_config);

			py_config.faulthandler = 0;
			py_config.install_signal_handlers = 0;

			for (auto&& module_search_path : python_state::default_module_search_paths) {
				PyWideStringList_Append(&py_config.module_search_paths, module_search_path.c_str());
			}
			PyWideStringList_Append(&py_config.module_search_paths, etc_irods_path.generic_wstring().c_str());
			py_config.module_search_paths_set = 1;

			PyStatus py_status = Py_InitializeFromConfig(&py_config);

			if (!PyStatus_Exception(py_status)) {
				return;
			}

			// clang-format off
			log_re::error({
				{"rule_engine_plugin", rule_engine_name},
				{"instance_name", _instance_name},
				{"log_message", "failed to initialize interpreter with PyConfig; falling back to legacy initialization"},
				{"PyStatus.exitcode", fmt::to_string(py_status.exitcode)},
				{"PyStatus.err_msg", py_status.err_msg},
				{"PyStatus.func", py_status.func},
			});
			// clang-format on
		}
#endif

		Py_InitializeEx(0);
#if PY_VERSION_HEX < 0x03070000
		PyEval_InitThreads();
#endif
		bp::object mod_sys = bp::import("sys");
		bp::list sys_path = bp::extract<bp::list>(mod_sys.attr("path"));
		sys_path.append(bp::str(etc_irods_path.generic_string().c_str()));
	}

} // anonymous namespace

static irods::error start(irods::default_re_ctx&, const std::string& _instance_name)
{
	python_state::ts_main = nullptr;

	irods::error ret = get_re_configs(_instance_name);
	if (!ret.ok()) {
		// clang-format off
		log_re::error({
			{"rule_engine_plugin", rule_engine_name},
			{"log_message", "Error loading plugin configuration"},
			{"instance_name", _instance_name},
			{"error_result", ret.result()},
		});
		// clang-format on
		return ret;
	}

	try {
		PyImport_AppendInittab("plugin_wrappers", &PyInit_plugin_wrappers);
		PyImport_AppendInittab("irods_types", &PyInit_irods_types);
		PyImport_AppendInittab("irods_errors", &PyInit_irods_errors);

		initialize_python(_instance_name);

		bp::object plugin_wrappers = bp::import("plugin_wrappers");
		bp::object irods_types = bp::import("irods_types");
		bp::object irods_errors = bp::import("irods_errors");

		StringFromPythonUnicode::register_converter();
	}
	catch (const bp::error_already_set&) {
		const std::string formatted_python_exception = extract_python_exception();
		// clang-format off
		log_re::error({
			{"rule_engine_plugin", rule_engine_name},
			{"instance_name", _instance_name},
			{"log_message", "caught python exception"},
			{"python_exception", formatted_python_exception},
		});
		// clang-format on
		std::string err_msg = std::string("irods_rule_engine_plugin_python::") + __PRETTY_FUNCTION__ +
		                      " Caught Python exception.\n" + formatted_python_exception;
		return ERROR(RULE_ENGINE_ERROR, err_msg);
	}

	python_state::ts_main = PyEval_SaveThread();
	// NO MORE PYTHON IN THIS FUNCTION PAST THIS POINT

	// Initialize microservice table
	irods::ms_table& ms_table = get_microservice_table();
	// writeLine is not in the microservice table in 4.2.0 - #3408
	if (!ms_table.has_entry("writeLine")) {
		ms_table["writeLine"] = new irods::ms_table_entry(
			"writeLine", 2, std::function<int(msParam_t*, msParam_t*, ruleExecInfo_t*)>(writeLine));
	}

	ms_table["py_remote"] = new irods::ms_table_entry(
		"py_remote",
		4,
		std::function<int(msParam_t*, msParam_t*, msParam_t*, msParam_t*, ruleExecInfo_t*)>(remote_exec_msvc));

	for (const auto& re_pep_regex : plugin_configuration::re_pep_regex_set) {
		RuleExistsHelper::Instance()->registerRuleRegex(re_pep_regex);
	}

	return SUCCESS();
}

static irods::error stop(irods::default_re_ctx&, const std::string&)
{
	PyEval_RestoreThread(python_state::ts_main);
	// Boost.Python's documentation advises not to call Py_Finalize
	// https://www.boost.org/doc/libs/1_78_0/libs/python/doc/html/tutorial/tutorial/embedding.html
	//Py_Finalize();
	return SUCCESS();
}

static irods::error rule_exists(const irods::default_re_ctx&, const std::string& rule_name, bool& _return)
{
	_return = false;
	python_gil_lock gil_lock;
	try {
		// TODO Enable non core.py Python rulebases
		bp::object core_module = bp::import("core");
		_return = PyObject_HasAttrString(core_module.ptr(), rule_name.c_str());
	}
	catch (const bp::error_already_set&) {
		const std::string formatted_python_exception = extract_python_exception();
		python_gil_unlock gil_release(&gil_lock, false);
		// clang-format off
		log_re::error({
			{"rule_engine_plugin", rule_engine_name},
			{"log_message", "caught python exception"},
			{"python_exception", formatted_python_exception},
		});
		// clang-format on
		std::string err_msg = std::string("irods_rule_engine_plugin_python::") + __PRETTY_FUNCTION__ +
		                      " Caught Python exception.\n" + formatted_python_exception;
		return ERROR(RULE_ENGINE_ERROR, err_msg);
	}
	// NOTE: If adding more catch blocks, nest this try/catch in another try block
	// along with the gil_lock definition. They need to stay in-scope for extract_python_exception,
	// but should be out of scope for other exception handlers.

	return SUCCESS();
}

static irods::error list_rules(const irods::default_re_ctx&, std::vector<std::string>& rule_vec)
{
	try {
		python_gil_lock gil_lock;
		// gil_lock needs to stay in scope for extract_python_exception
		// hence the nested exception handling
		try {
			bp::object core_module = bp::import("core");
			bp::object core_namespace = core_module.attr("__dict__");

			bp::exec("import inspect\n"
			         "import sys\n"
			         "function_list = inspect.getmembers(sys.modules['core'], inspect.isfunction)\n"
			         "function_names = [ tup[0] for tup in function_list ]\n",
			         core_namespace,
			         core_namespace);

			bp::list function_names = bp::extract<bp::list>(core_namespace["function_names"]);

			std::size_t len_names = bp::extract<std::size_t>(function_names.attr("__len__")());
			for (std::size_t i = 0; i < len_names; ++i) {
				rule_vec.push_back(bp::extract<std::string>(function_names[i]));
				std::string tmp = bp::extract<std::string>(function_names[i]);
			}
		}
		catch (const bp::error_already_set&) {
			const std::string formatted_python_exception = extract_python_exception();
			python_gil_unlock gil_release(&gil_lock, false);
			// clang-format off
			log_re::error({
				{"rule_engine_plugin", rule_engine_name},
				{"log_message", "caught python exception"},
				{"python_exception", formatted_python_exception},
			});
			// clang-format on
			auto start_pos = formatted_python_exception.find(IRODS_ERROR_PREFIX);
			int error_code_int = -1;
			if (start_pos != std::string::npos) {
				start_pos += IRODS_ERROR_PREFIX.size();
				auto end_pos = formatted_python_exception.find_first_of("]", start_pos);
				std::string error_code = formatted_python_exception.substr(start_pos, end_pos - start_pos);
				error_code_int = boost::lexical_cast<int>(error_code);
			}
			std::string err_msg = std::string("irods_rule_engine_plugin_python::") + __PRETTY_FUNCTION__ +
			                      " Caught Python exception.\n" + formatted_python_exception;
			return ERROR(error_code_int, err_msg);
		}
	}
	catch (const boost::bad_any_cast& e) {
		// clang-format off
		log_re::error({
			{"rule_engine_plugin", rule_engine_name},
			{"log_message", "bad any cast"},
			{"exception", e.what()},
		});
		// clang-format on
		std::string err_msg =
			std::string("irods_rule_engine_plugin_python::") + __PRETTY_FUNCTION__ + " bad_any_cast : " + e.what();
		return ERROR(INVALID_ANY_CAST, e.what());
	}

	return SUCCESS();
}

static irods::error exec_rule(const irods::default_re_ctx&,
                              const std::string& rule_name,
                              std::list<boost::any>& rule_arguments_cpp,
                              irods::callback effect_handler)
{
	try {
		python_gil_lock gil_lock;
		// gil_lock needs to stay in scope for extract_python_exception
		// hence the nested exception handling
		try {
			// TODO Enable non core.py Python rulebases
			bp::object core_module = bp::import("core");
			bp::object core_namespace = core_module.attr("__dict__");
			bp::object irods_types = bp::import("irods_types");
			bp::object irods_errors = bp::import("irods_errors");

			core_namespace["irods_types"] = irods_types;
			core_namespace["irods_errors"] = irods_errors;

			bp::object rule_function = core_module.attr(rule_name.c_str());

			const auto rei = get_rei_from_effect_handler(effect_handler);
			bp::list rule_arguments_python{};
			for (auto& cpp_argument : rule_arguments_cpp) {
				rule_arguments_python.append(object_from_any(cpp_argument));
			}

			const bp::object ec = rule_function(rule_arguments_python, CallbackWrapper{effect_handler}, rei);

			int i = 0;
			for (auto& cpp_argument : rule_arguments_cpp) {
				bp::object py_argument = rule_arguments_python[i];
				update_argument(cpp_argument, py_argument);
				++i;
			}

			return to_irods_error_object(ec);
		}
		catch (const bp::error_already_set&) {
			const std::string formatted_python_exception = extract_python_exception();
			// clang-format off
			python_gil_unlock gil_release(&gil_lock, false);
			log_re::error({
				{"rule_engine_plugin", rule_engine_name},
				{"log_message", "caught python exception"},
				{"python_exception", formatted_python_exception},
			});
			// clang-format on
			auto start_pos = formatted_python_exception.find(IRODS_ERROR_PREFIX);
			int error_code_int = -1;
			if (start_pos != std::string::npos) {
				start_pos += IRODS_ERROR_PREFIX.size();
				auto end_pos = formatted_python_exception.find_first_of("]", start_pos);
				std::string error_code = formatted_python_exception.substr(start_pos, end_pos - start_pos);
				error_code_int = boost::lexical_cast<int>(error_code);
			}
			std::string err_msg = std::string("irods_rule_engine_plugin_python::") + __PRETTY_FUNCTION__ +
			                      " Caught Python exception.\n" + formatted_python_exception;
			return ERROR(error_code_int, err_msg);
		}
	}
	catch (const boost::bad_any_cast& e) {
		// clang-format off
		log_re::error({
			{"rule_engine_plugin", rule_engine_name},
			{"log_message", "bad any cast"},
			{"exception", e.what()},
		});
		// clang-format on
		std::string err_msg =
			std::string("irods_rule_engine_plugin_python::") + __PRETTY_FUNCTION__ + " bad_any_cast : " + e.what();
		return ERROR(INVALID_ANY_CAST, e.what());
	}
	catch (...) {
		// clang-format off
		log_re::error({
			{"rule_engine_plugin", rule_engine_name},
			{"log_message", "Caught unknown exception"},
		});
		// clang-format on
		return ERROR(SYS_UNKNOWN_ERROR, "Caught unknown exception.");
	}

	return SUCCESS();
}

//irule
static irods::error exec_rule_text(const irods::default_re_ctx&,
                                   const std::string& rule_text,
                                   msParamArray_t* ms_params,
                                   const std::string& out_desc,
                                   irods::callback effect_handler)
{
	// Because Python is not sandboxed, need to restrict irule to admin users only
	const auto rei = get_rei_from_effect_handler(effect_handler);

	if (!rei) {
		// clang-format off
		log_re::error({
			{"rule_engine_plugin", rule_engine_name},
			{"log_message", "RuleExecInfo object is NULL - cannot authenticate user"},
		});
		// clang-format on
		return ERROR(NULL_VALUE_ERR, "Null rei pointer in exec_rule_text");
	}

	int client_user_authflag = 0;
	if (rei->uoic) {
		client_user_authflag = rei->uoic->authInfo.authFlag;
	}
	else if (rei->rsComm) {
		client_user_authflag = rei->rsComm->clientUser.authInfo.authFlag;
	}

	int proxy_user_authflag = 0;
	if (rei->uoip) {
		proxy_user_authflag = rei->uoip->authInfo.authFlag;
	}
	else if (rei->rsComm) {
		proxy_user_authflag = rei->rsComm->proxyUser.authInfo.authFlag;
	}

	if ((client_user_authflag < REMOTE_PRIV_USER_AUTH) || (proxy_user_authflag < REMOTE_PRIV_USER_AUTH)) {
		// clang-format off
		log_re::debug({
			{"rule_engine_plugin", rule_engine_name},
			{"log_message", "Insufficient privileges to run irule in Python rule engine plugin"},
		});
		// clang-format on
		return ERROR(SYS_NO_API_PRIV, "Insufficient privileges to run irule in Python rule engine plugin");
	}

	try {
		python_gil_lock gil_lock;
		// gil_lock needs to stay in scope for extract_python_exception
		// hence the nested exception handling
		try {
			execCmdOut_t* myExecCmdOut = (execCmdOut_t*) malloc(sizeof(*myExecCmdOut));
			memset(myExecCmdOut, 0, sizeof(*myExecCmdOut));

			addMsParam(ms_params, out_desc.c_str(), ExecCmdOut_MS_T, myExecCmdOut, NULL);

			// Convert INPUT and OUTPUT rule vars to Python dict
			bp::dict rule_vars_python;

			int i = 0;
			for (i = 0; i < ms_params->len; i++) {
				msParam_t* mp = ms_params->msParam[i];
				std::string label(mp->label);

				if (mp->type == NULL) {
					rule_vars_python[label] = NULL;
				}
				else if (std::strcmp(mp->type, DOUBLE_MS_T) == 0) {
					double* tmpDouble = (double*) mp->inOutStruct;
					rule_vars_python[label] = tmpDouble;
				}
				else if (std::strcmp(mp->type, INT_MS_T) == 0) {
					int* tmpInt = (int*) mp->inOutStruct;
					rule_vars_python[label] = tmpInt;
				}
				else if (std::strcmp(mp->type, STR_MS_T) == 0) {
					char* tmpChar = (char*) mp->inOutStruct;
					std::string tmpStr(tmpChar);
					rule_vars_python[label] = tmpStr;
				}
				else if (std::strcmp(mp->type, DATETIME_MS_T) == 0) {
					rodsLong_t* tmpRodsLong = (rodsLong_t*) mp->inOutStruct;
					rule_vars_python[label] = tmpRodsLong;
				}
			}

			if (strncmp(rule_text.c_str(), "@external\n", 10) == 0) {
				// If rule_text begins with "@external\n", call is of form
				//  irule -F inputFile ...

				// Import rule INPUT and OUTPUT variables
				bp::object builtin_module = bp::import("builtins");
				builtin_module.attr("irods_rule_vars") = rule_vars_python;

				bp::object main_module = bp::import("__main__");
				bp::object main_namespace = main_module.attr("__dict__");
				bp::object irods_types = bp::import("irods_types");
				bp::object irods_errors = bp::import("irods_errors");

				// deprecated alias for irods_rule_vars
				main_namespace["global_vars"] = rule_vars_python;

				// Import global constants
				main_namespace["irods_types"] = irods_types;
				main_namespace["irods_errors"] = irods_errors;

				// Parse input rule_text into useable Python fcns
				// Delete first line ("@external")
				std::string trimmed_rule = rule_text.substr(rule_text.find_first_of('\n') + 1);

				bp::exec(trimmed_rule.c_str(), main_namespace, main_namespace);
				bp::object rule_function = main_module.attr("main");

				bp::list rule_arguments_python{};
				return to_irods_error_object(
					rule_function(rule_arguments_python, CallbackWrapper{effect_handler}, rei));
			}
			else if (strncmp(rule_text.c_str(), "@external rule", 14) == 0) {
				// If rule_text begins with "@external ", call is of form
				//  irule rule ...

				// Import rule INPUT and OUTPUT variables
				bp::object builtin_module = bp::import("builtins");
				builtin_module.attr("irods_rule_vars") = rule_vars_python;

				// TODO Enable non core.py Python rulebases
				bp::object core_module = bp::import("core");
				bp::object core_namespace = core_module.attr("__dict__");

				// deprecated alias for irods_rule_vars
				core_namespace["global_vars"] = rule_vars_python;

				// Delete "@external rule { " from the start of the rule_text
				std::string trimmed_rule = rule_text.substr(17);

				// Extract rule name ("@external rule { RULE_NAME }")
				std::string rule_name = trimmed_rule.substr(0, trimmed_rule.find_first_of(' '));

				bp::object rule_function = core_module.attr(rule_name.c_str());

				bp::list rule_arguments_python{};
				return to_irods_error_object(
					rule_function(rule_arguments_python, CallbackWrapper{effect_handler}, rei));
			}
			else {
				python_gil_unlock gil_release(&gil_lock, false);
				// clang-format off
				log_re::error({
					{"rule_engine_plugin", rule_engine_name},
					{"log_message", "Improperly formatted rule text"},
				});
				// clang-format on
				return ERROR(RULE_ENGINE_ERROR, "Improperly formatted rule_text");
			}
		}
		catch (const bp::error_already_set&) {
			const std::string formatted_python_exception = extract_python_exception();
			python_gil_unlock gil_release(&gil_lock, false);
			// clang-format off
			log_re::error({
				{"rule_engine_plugin", rule_engine_name},
				{"log_message", "caught python exception"},
				{"python_exception", formatted_python_exception},
			});
			// clang-format on
			std::string err_msg = std::string("irods_rule_engine_plugin_python::") + __PRETTY_FUNCTION__ +
			                      " Caught Python exception.\n" + formatted_python_exception;
			return ERROR(RULE_ENGINE_ERROR, err_msg);
		}
	}
	catch (const boost::bad_any_cast& e) {
		// clang-format off
		log_re::error({
			{"rule_engine_plugin", rule_engine_name},
			{"log_message", "bad any cast"},
			{"exception", e.what()},
		});
		// clang-format on
		std::string err_msg =
			std::string("irods_rule_engine_plugin_python::") + __PRETTY_FUNCTION__ + " bad_any_cast : " + e.what();
		return ERROR(INVALID_ANY_CAST, e.what());
	}
	catch (...) {
		// clang-format off
		log_re::error({
			{"rule_engine_plugin", rule_engine_name},
			{"log_message", "Caught unknown exception"},
		});
		// clang-format on
		return ERROR(SYS_UNKNOWN_ERROR, "Caught unknown exception.");
	}

	return SUCCESS();
}

//delay execution
static irods::error exec_rule_expression(irods::default_re_ctx&,
                                         const std::string& rule_text,
                                         msParamArray_t* ms_params,
                                         irods::callback effect_handler)
{
	try {
		python_gil_lock gil_lock;
		// gil_lock needs to stay in scope for extract_python_exception
		// hence the nested exception handling
		try {
			bp::dict rule_vars_python;

			// Convert INPUT/OUTPUT rule vars to Python dict
			if (ms_params) {
				for (int i = 0; i < ms_params->len; i++) {
					if (msParam_t* mp = ms_params->msParam[i]) {
						std::string label(mp->label);

						if (mp->type == NULL) {
							rule_vars_python[label] = boost::python::object{};
						}
						else if (std::strcmp(mp->type, DOUBLE_MS_T) == 0) {
							double* tmpDouble = (double*) mp->inOutStruct;
							rule_vars_python[label] = tmpDouble;
						}
						else if (std::strcmp(mp->type, INT_MS_T) == 0) {
							int* tmpInt = (int*) mp->inOutStruct;
							rule_vars_python[label] = tmpInt;
						}
						else if (std::strcmp(mp->type, STR_MS_T) == 0) {
							char* tmpChar = (char*) mp->inOutStruct;
							std::string tmpStr(tmpChar);
							rule_vars_python[label] = tmpStr;
						}
						else if (std::strcmp(mp->type, DATETIME_MS_T) == 0) {
							rodsLong_t* tmpRodsLong = (rodsLong_t*) mp->inOutStruct;
							rule_vars_python[label] = tmpRodsLong;
						}
					}
				}
			}

			// Import rule INPUT and OUTPUT variables
			bp::object builtin_module = bp::import("builtins");
			builtin_module.attr("irods_rule_vars") = rule_vars_python;

			// Parse input rule_text into useable Python fcns
			bp::object main_module = bp::import("__main__");
			bp::object irods_types = bp::import("irods_types");
			bp::object irods_errors = bp::import("irods_errors");
			bp::object main_namespace = main_module.attr("__dict__");

			// deprecated alias for irods_rule_vars
			main_namespace["global_vars"] = rule_vars_python;

			// Import globals
			main_namespace["irods_types"] = irods_types;
			main_namespace["irods_errors"] = irods_errors;

			// Add def expressionFcn(rule_args, callback):\n to start of rule text
			std::string rule_name = "expressionFcn";
			std::string fcn_text = "def " + rule_name + "(rule_args, callback, rei):\n" + rule_text;
			// Replace every '\n' with '\n '
			boost::replace_all(fcn_text, "\n", "\n ");
			bp::exec(fcn_text.c_str(), main_namespace, main_namespace);
			bp::object rule_function = main_module.attr(rule_name.c_str());

			const auto rei = get_rei_from_effect_handler(effect_handler);
			bp::list rule_arguments_python{};
			return to_irods_error_object(rule_function(rule_arguments_python, CallbackWrapper{effect_handler}, rei));
		}
		catch (const bp::error_already_set&) {
			const std::string formatted_python_exception = extract_python_exception();
			python_gil_unlock gil_release(&gil_lock, false);
			// clang-format off
			log_re::error({
				{"rule_engine_plugin", rule_engine_name},
				{"log_message", "caught python exception"},
				{"python_exception", formatted_python_exception},
			});
			// clang-format on
			std::string err_msg = std::string("irods_rule_engine_plugin_python::") + __PRETTY_FUNCTION__ +
			                      " Caught Python exception.\n" + formatted_python_exception;
			return ERROR(RULE_ENGINE_ERROR, err_msg);
		}
	}
	catch (const boost::bad_any_cast& e) {
		// clang-format off
		log_re::error({
			{"rule_engine_plugin", rule_engine_name},
			{"log_message", "bad any cast"},
			{"exception", e.what()},
		});
		// clang-format on
		std::string err_msg =
			std::string("irods_rule_engine_plugin_python::") + __PRETTY_FUNCTION__ + " bad_any_cast : " + e.what();
		return ERROR(INVALID_ANY_CAST, e.what());
	}
	catch (...) {
		// clang-format off
		log_re::error({
			{"rule_engine_plugin", rule_engine_name},
			{"log_message", "Caught unknown exception"},
		});
		// clang-format on
		return ERROR(SYS_UNKNOWN_ERROR, "Caught unknown exception.");
	}

	return SUCCESS();
}

extern "C" irods::pluggable_rule_engine<irods::default_re_ctx>* plugin_factory(const std::string& _inst_name,
                                                                               const std::string& _context)
{
	irods::pluggable_rule_engine<irods::default_re_ctx>* re =
		new irods::pluggable_rule_engine<irods::default_re_ctx>(_inst_name, _context);
	re->add_operation<irods::default_re_ctx&, const std::string&>(
		"start", std::function<irods::error(irods::default_re_ctx&, const std::string&)>(start));

	re->add_operation<irods::default_re_ctx&, const std::string&>(
		"stop", std::function<irods::error(irods::default_re_ctx&, const std::string&)>(stop));

	re->add_operation<irods::default_re_ctx&, const std::string&, bool&>(
		"rule_exists", std::function<irods::error(irods::default_re_ctx&, const std::string&, bool&)>(rule_exists));

	re->add_operation<irods::default_re_ctx&, std::vector<std::string>&>(
		"list_rules", std::function<irods::error(irods::default_re_ctx&, std::vector<std::string>&)>(list_rules));

	re->add_operation<irods::default_re_ctx&, const std::string&, std::list<boost::any>&, irods::callback>(
		"exec_rule",
		std::function<irods::error(
			irods::default_re_ctx&, const std::string&, std::list<boost::any>&, irods::callback)>(exec_rule));

	re->add_operation<irods::default_re_ctx&, const std::string&, msParamArray_t*, const std::string&, irods::callback>(
		"exec_rule_text",
		std::function<irods::error(
			irods::default_re_ctx&, const std::string&, msParamArray_t*, const std::string&, irods::callback)>(
			exec_rule_text));

	re->add_operation<irods::default_re_ctx&, const std::string&, msParamArray_t*, irods::callback>(
		"exec_rule_expression",
		std::function<irods::error(irods::default_re_ctx&, const std::string&, msParamArray_t*, irods::callback)>(
			exec_rule_expression));

#if PY_VERSION_HEX >= 0x03080000
	Py_InitializeEx(0);
	try {
		bp::object mod_sys = bp::import("sys");
		bp::list sys_path = bp::extract<bp::list>(mod_sys.attr("path"));
		std::size_t sys_path_len = bp::extract<std::size_t>(sys_path.attr("__len__")());
		python_state::default_module_search_paths.reserve(sys_path_len);
		for (std::size_t i = 0; i < sys_path_len; ++i) {
			python_state::default_module_search_paths.push_back(bp::extract<std::wstring>(sys_path[i]));
		}
		python_state::default_module_search_paths_set = true;
	}
	catch (const bp::error_already_set&) {
		const std::string formatted_python_exception = extract_python_exception();
		// clang-format off
		log_re::error({
			{"rule_engine_plugin", rule_engine_name},
			{"instance_name", _inst_name},
			{"log_message", "caught python exception in plugin factory; will use legacy module search path initialization"},
			{"python_exception", formatted_python_exception},
		});
		// clang-format on
		python_state::default_module_search_paths.clear();
		python_state::default_module_search_paths.shrink_to_fit();
		python_state::default_module_search_paths_set = false;
	}
	Py_Finalize(); // We're not supposed to do this, but let's try it anyway.
#endif

	return re;
}
