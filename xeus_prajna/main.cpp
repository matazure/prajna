
#include <iostream>

#include "prajna_xeus_interpreter.hpp"
#include "xeus-zmq/xserver_shell_main.hpp"
#include "xeus/xkernel.hpp"
#include "xeus/xkernel_configuration.hpp"

int main(int argc, char* argv[]) {
    auto uq_xeus_prajna_interpreter = std::make_unique<xeus_prajna::PrajnaXeusInterpreter>();
    // Registering SIGSEGV handler
    // Load configuration file
    std::string file_name = std::string(argv[2]);

    auto context = xeus::make_context<zmq::context_t>();

    // Create kernel instance and start it
    // xeus::xkernel kernel(config, xeus::get_user_name(), std::move(interpreter));
    // kernel.start();
    using history_manager_ptr = std::unique_ptr<xeus::xhistory_manager>;
    history_manager_ptr hist = xeus::make_in_memory_history_manager();

    if (!file_name.empty()) {
        xeus::xconfiguration config = xeus::load_configuration(file_name);

        xeus::xkernel kernel(
            config, xeus::get_user_name(), std::move(context),
            std::move(uq_xeus_prajna_interpreter), xeus::make_xserver_shell_main, std::move(hist),
            xeus::make_console_logger(xeus::xlogger::msg_type,
                                      xeus::make_file_logger(xeus::xlogger::content, "xeus.log")));

        std::clog << "Starting xeus-prajna kernel...\n\n"
                     "If you want to connect to this kernel from an other client, you can use"
                     " the " +
                         file_name + " file."
                  << std::endl;

        kernel.start();
    } else {
        xeus::xkernel kernel(xeus::get_user_name(), std::move(context),
                             std::move(uq_xeus_prajna_interpreter), xeus::make_xserver_shell_main,
                             std::move(hist), nullptr);

        const auto& config = kernel.get_config();
        std::clog << "Starting xeus-prajna kernel...\n\n"
                     "If you want to connect to this kernel from an other client, just copy"
                     " and paste the following content inside of a `kernel.json` file. And then "
                     "run for example:\n\n"
                     "# jupyter console --existing kernel.json\n\n"
                     "kernel.json\n```\n{\n"
                     "    \"transport\": \"" +
                         config.m_transport +
                         "\",\n"
                         "    \"ip\": \"" +
                         config.m_ip +
                         "\",\n"
                         "    \"control_port\": " +
                         config.m_control_port +
                         ",\n"
                         "    \"shell_port\": " +
                         config.m_shell_port +
                         ",\n"
                         "    \"stdin_port\": " +
                         config.m_stdin_port +
                         ",\n"
                         "    \"iopub_port\": " +
                         config.m_iopub_port +
                         ",\n"
                         "    \"hb_port\": " +
                         config.m_hb_port +
                         ",\n"
                         "    \"signature_scheme\": \"" +
                         config.m_signature_scheme +
                         "\",\n"
                         "    \"key\": \"" +
                         config.m_key +
                         "\"\n"
                         "}\n```\n";

        kernel.start();
    }

    return 0;
}
