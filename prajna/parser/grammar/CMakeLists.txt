add_library(prajna_grammar statement_grammar.cpp expression_grammar.cpp)
target_link_libraries(prajna_grammar
    PUBLIC prajna_ast
    PRIVATE Boost::spirit
    PUBLIC prajna_lexer
)

if (PRAJNA_SPIRIT_DEBUG)
    message(FATAL_ERROR "不在支持BOOST_SPIRIT_DEBUG, 用处不大不如直接调式源代码")
    target_compile_definitions(prajna_grammar PRIVATE BOOST_SPIRIT_DEBUG)
endif()
