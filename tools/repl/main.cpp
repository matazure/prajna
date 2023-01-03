#include <exception>
#include <functional>
#include <iostream>
#include <list>
#include <stdexcept>
#include <string>
#include <vector>

#include "cpp-terminal/input.hpp"
#include "cpp-terminal/prompt.hpp"
#include "prajna/compiler/compiler.h"
#include "prajna/helper.hpp"

using Term::Key;
using Term::prompt_multiline;
using Term::Terminal;

bool determine_completeness(CPP_TERMINAL_MAYBE_UNUSED std::string command) {
    // Determine if the statement is complete
    bool complete;
    if (command.size() > 1 && command.substr(command.size() - 2, 1) == "\\") {
        complete = false;
    } else {
        complete = true;
    }
    return complete;
}

int main() {
    std::cout << "Prajna 0.0, all copyrights @ \"Zhang Zhimin\"" << std::endl;

    auto compiler = prajna::Compiler::create();
    compiler->compileBuiltinSourceFiles("prajna/builtin_sources");

    Term::Terminal term(false, true, false, false);
    std::vector<std::string> history;
    while (true) {
        std::function<bool(std::string)> iscomplete = [](std::string code_line) {
            return code_line.empty() || code_line[code_line.size() - 2] != '\\';
        };
        std::string code_line = Term::prompt_multiline(term, "prajna > ", history, iscomplete);

        if (code_line.size() == 1 && code_line[0] == Term::Key::CTRL_D) break;
        if (code_line == "quit") break;

        // 移除换行符号 '\\'
        std::list<char> code_line_list(RANGE(code_line));
        for (auto iter = code_line_list.begin(); iter != std::prev(code_line_list.end());) {
            if (*iter == '\\') {
                if ((*std::next(iter)) == '\n' or (*std::next(iter)) == '\r') {
                    iter = code_line_list.erase(iter);
                    continue;
                }
            }

            ++iter;
        }
        code_line = std::string(RANGE(code_line_list));
        // ;可以重复, 不会导致错误. 插入到\n前面, 这样错误信息才正确
        auto last_char = *std::prev(code_line.end(), 2);
        if (code_line.size() >= 2 and not(last_char == ';' or last_char == '}')) {
            code_line.insert(std::prev(code_line.end()), ';');
        }
        // code_line.push_back('\n'); // 自带\n
        compiler->compileCommandLine(code_line);

        std::cout << "\n";
    }

    return 0;
}
