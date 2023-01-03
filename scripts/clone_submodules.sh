#! /bin/bash
set -e


# 下载子模块
git submodule init .
git submodule update --depth=1

# 下载boost的子模块
cd third_party/boost
git submodule init libs/spirit
git submodule init libs/algorithm
git submodule init libs/range
git submodule init libs/variant
git submodule init libs/optional
git submodule init libs/fusion
git submodule init libs/spirit
git submodule init libs/multiprecision
git submodule init libs/describe
git submodule init libs/function_types
git submodule init tools/cmake
git submodule init libs/mpl
git submodule init libs/endian
git submodule init libs/pool
git submodule init libs/phoenix
git submodule init libs/preprocessor
git submodule init libs/proto
git submodule init libs/regex
git submodule init libs/thread
git submodule init libs/type_traits
git submodule init libs/typeof
git submodule init libs/unordered
git submodule init libs/assert
git submodule init libs/core
git submodule init libs/integer
git submodule init libs/predef
git submodule init libs/throw_exception
git submodule init libs/type_index
git submodule init libs/tuple
git submodule init libs/container_hash
git submodule init libs/array
git submodule init libs/iterator
git submodule init libs/static_assert
git submodule init libs/lexical_cast
git submodule init libs/detail
git submodule init libs/config
git submodule init libs/bind
git submodule init libs/chrono
git submodule init libs/container
git submodule init libs/date_time
git submodule init libs/exception
git submodule init libs/function
git submodule init libs/functional
git submodule init libs/concept_check
git submodule init libs/intrusive
git submodule init libs/io
git submodule init libs/move
git submodule init libs/smart_ptr
git submodule init libs/system
git submodule init libs/utility
git submodule init libs/winapi
git submodule init libs/ratio
git submodule init libs/variant2
git submodule init libs/conversion
git submodule init libs/numeric
git submodule init libs/tokenizer
git submodule init libs/atomic
git submodule init libs/random
git submodule init libs/math
git submodule init libs/rational
git submodule init libs/align
git submodule init libs/mp11
git submodule init libs/dynamic_bitset

git submodule update --depth=1
