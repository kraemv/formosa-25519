#!/usr/bin/env bash

# pro user tip (because this repository shares the same structure as in libjade); assumes libjade is next to formosa-25519
#
# ./extract-libjade.sh --list-implementations | while read implementation; do ./extract-libjade.sh --gen-implementation $implementation ../libjade/src/$implementation; done

stderr() {
  echo >&2 "${@}"
}

print_usage() {
  stderr "usage:"
  stderr " \$ ${call} --list-implementations"
  stderr " \$ ${call} --gen-implementation IMPLEMENTATION DIRECTORY"
}

fatal_usage() {
  if (( "$#" != 0 )); then
    stderr "error:" "$@"
  fi
  print_usage
  exit 1
}

main() {
  call="${0}"
  top_dir="$(cd "$(dirname "${0}")" ; pwd -P)" || exit 1

  # if there are no arguments, print usage
  if (( "${#}" == 0 )); then
    fatal_usage
  fi

  # check if --list-implementations
  if [ "${1}" == "--list-implementations" ]; then
    make --no-print-directory -C "$top_dir"/src print-available-implementations
    exit 1
  fi

  # check if --gen-implementation
  if [ "${1}" == "--gen-implementation" ]; then
   # if we are generating an implementation then there should be 3 args
   if [ "${#}" -eq 3 ]; then

     # start by realpath them (useful to run make)
     implementation="$top_dir"/src/$2
     directory=$3

     # test if IMPLEMENTATION directory exists
     if [ ! -d "${implementation}" ]; then
       stderr " IMPLEMENTATION: ${implementation} does not exist."
       exit 1;
     fi

    # test if libjade DIRECTORY exists
    if [ ! -d "${directory}" ]; then
       stderr " DIRECTORY: ${directory} does not exist."
       exit 1;
    fi

    relative_implementation="$(realpath --relative-to="${top_dir}/src" "${implementation}")"
    make --no-print-directory -C "${top_dir}/src/" "${relative_implementation}/preprocess-inplace"

    #############################################################################
    # copy the preprocessed files

    jazz_files="$(find "${implementation}" -name '*.jazz')"
    for file in $jazz_files; do
      cp "$file" "$directory"/
    done

    # setup the Makefile
    echo -n "SRCS := " > "${directory}/Makefile"
    for file in $jazz_files; do
      echo -n "$(basename "${file}")" >> "${directory}/Makefile"
    done
    echo "" >> "${directory}/Makefile"

    # NOTE: the following line will need change (or be deleted) once multi-repo libjade is stable
    echo "include ../../../../Makefile.common" >> "${directory}/Makefile"

    # NOTE: the following command will change once there is a PR in libjade to move api.h files out of include/ directories
    cp "${implementation}/include/api.h" "${directory}/include/api.h"

    #
    #############################################################################

    # restore implementation state
    make --no-print-directory -C "${top_dir}/src/" "${relative_implementation}/revert-preprocess-inplace"

    exit 1;

   else
    fatal_usage "$0 --gen-implementation: number of required arguments 3 : provided $#"
   fi
  fi

  # with 'good' options this should be unreachable, hence, print usage
  print_usage
  exit 1
}

init() {
  set -e
  main "${@}"
}

init "${@}"
