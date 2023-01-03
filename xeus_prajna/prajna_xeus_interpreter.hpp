#pragma once

#include <filesystem>

#include "prajna/compiler/compiler.h"
#include "xeus/xinterpreter.hpp"

namespace xeus_prajna {

class PrajnaXeusInterpreter : public xeus::xinterpreter {
   public:
    PrajnaXeusInterpreter() {
        compiler = prajna::Compiler::create();
        compiler->compileBuiltinSourceFiles("builtin_sources");
    }

    virtual ~PrajnaXeusInterpreter() = default;

   private:
    void configure_impl() override {}

    nl::json execute_request_impl(int execution_counter, const std::string& code, bool silent,
                                  bool store_history, nl::json user_expressions,
                                  bool allow_stdin) override {
        nl::json result;
        prajna::print_callback = [=, &result, compiler = compiler](const char* c_str) {
            nl::json pub_data;
            pub_data["text/plain"] = std::string(c_str);
            publish_execution_result(execution_counter, pub_data, nl::json::object());
        };

        auto code_line = code;
        if (code_line.size() >= 1 and not(code_line.back() == ';' or code_line.back() == '}')) {
            code_line.push_back(';');
        }
        code_line.push_back('\n');
        compiler->compileCommandLine(code_line);

        result["status"] = "ok";
        result["payload"] = nl::json::array();
        result["user_expressions"] = nl::json::object();
        return result;

        return result;
    }

    nl::json complete_request_impl(const std::string& code, int cursor_pos) override {
        nl::json result;
        result["status"] = "ok";
        return result;
    }

    nl::json inspect_request_impl(const std::string& code, int cursor_pos,
                                  int detail_level) override {
        nl::json result;
        result["status"] = "ok";
        return result;
    }

    /// @brief 并非必须的,故直接放回complete的状态
    nl::json is_complete_request_impl(const std::string& code) override {
        nl::json result;
        result["status"] = "complete";
        return result;
    }

    nl::json kernel_info_request_impl() override {
        nl::json result;
        const std::string PRAJNA_VERSION = "0.0.0";
        result["implementation"] = "xprajna";
        result["implementation_version"] = PRAJNA_VERSION;

        std::string banner =
            ""
            "  __  _____ _   _ ___\n"
            "  \\ \\/ / _ \\ | | / __|\n"
            "   >  <  __/ |_| \\__ \\\n"
            "  /_/\\_\\___|\\__,_|___/\n"
            "\n"
            "  xeus-prajna: a Jupyter Kernel for Prajna\n";
        result["banner"] = banner;
        result["language_info"]["name"] = "prajna";
        // result["language_info"]["codemirror_mode"] = "prajna";
        result["language_info"]["mimetype"] = "text/x-prajna";
        result["language_info"]["version"] = PRAJNA_VERSION;
        result["language_info"]["file_extension"] = ".prajna";

        return result;
    }
    void shutdown_request_impl() override {}

   private:
    std::shared_ptr<prajna::Compiler> compiler;
};

}  // namespace xeus_prajna
