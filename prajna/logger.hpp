#pragma once

#include <boost/algorithm/string.hpp>
#include <map>

#include "fmt/color.h"
#include "fmt/format.h"
#include "prajna/assert.hpp"
#include "prajna/ast/ast.hpp"
#include "prajna/exception.hpp"
#include "prajna/rich_bash.hpp"

namespace prajna {

enum struct LogLevel {
    info = 1,
    warning,
    error,
};
}

namespace fmt {

// @ref https://fmt.dev/latest/api.html#formatting-user-defined-types
template <>
struct formatter<prajna::LogLevel> {
    constexpr auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
        auto it = ctx.begin(), end = ctx.end();
        if (it != end && *it != '}') throw format_error("invalid format");
        return it;
    }

    template <typename FormatContext>
    auto format(const prajna::LogLevel& level, FormatContext& ctx) const -> decltype(ctx.out()) {
        // ctx.out() is an output iterator to write to.
        switch (level) {
            case prajna::LogLevel::info:
                return fmt::format_to(ctx.out(), "{}",
                                      fmt::styled("info", fmt::fg(fmt::color::gray)));
            case prajna::LogLevel::warning:
                return fmt::format_to(ctx.out(), "{}",
                                      fmt::styled("warning", fmt::fg(fmt::color::orange)));
            case prajna::LogLevel::error:
                return fmt::format_to(ctx.out(), "{}",
                                      fmt::styled("error", fmt::fg(fmt::color::red)));
        }

        return ctx.out();
    }
};

}  // namespace fmt

namespace prajna {

class CompileError {
   public:
    CompileError() = default;
};

class Logger {
   protected:
    Logger() = default;

   public:
    static std::shared_ptr<Logger> create(std::string code) {
        std::shared_ptr<Logger> self(new Logger);
        boost::split(self->_code_lines, code, boost::is_any_of("\n"));
        return self;
    }

    void error(std::string message, ast::SourcePosition first_position,
               ast::SourcePosition last_position, std::string ascii_color = std::string(BLU)) {
        if (first_position.file.empty()) {
            fmt::print("{}:{}: {}: {}\n", first_position.line, first_position.column,
                       fmt::styled("error", fmt::fg(fmt::color::red)), message);
        } else {
            fmt::print("{}:{}:{}: {}: {}\n", first_position.file, first_position.line,
                       first_position.column, fmt::styled("error", fmt::fg(fmt::color::red)),
                       message);
        }

        if (last_position.column - 1 > _code_lines[last_position.line - 1].size()) {
            std::string spaces(
                last_position.column - 1 - _code_lines[last_position.line - 1].size(), ' ');
            _code_lines[last_position.line - 1].append(spaces);
        }
        _code_lines[last_position.line - 1].insert(last_position.column - 1, std::string(RESET));
        // 不存在越界的情况
        PRAJNA_ASSERT(first_position.column - 1 >= 0);
        _code_lines[first_position.line - 1].insert(first_position.column - 1, ascii_color);
        std::string code_region;
        for (size_t i = first_position.line; i <= last_position.line; ++i) {
            PRAJNA_ASSERT(i - 1 >= 0 and i - 1 < _code_lines.size());
            code_region.append(_code_lines[i - 1]);
            code_region.append("\n");
        }

        // fmt::print(code_region); // has bug
        std::cout << code_region;

        throw CompileError();
    }

    void error(std::string message, ast::SourceLocation source_location) {
        error(message, source_location.first_position, source_location.last_position);
    }

    void error(std::string message, ast::Operand ast_operand) {
        boost::apply_visitor([&](auto x) { this->error(message, x); }, ast_operand);
    }

   private:
    std::vector<std::string> _code_lines;
};

}  // namespace prajna
