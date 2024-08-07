#!/usr/bin/env bash

# pro user tip (because this repository shares the same structure as in libjade); assumes libjade is next to formosa-25519
#
# ./extract-libjade.sh --list-implementations | while read implementation; do ./extract-libjade.sh --gen-implementation $implementation ../libjade/src/$implementation; done

stderr() {
  echo >&2 "${@}"
}

fatal() {
  if (( "$#" == 0 )); then
    fatal "Some error ocurred"
  else
    stderr "error:" "$@"
    exit 1
  fi
}

fatal_abspath_usage() {
  fatal "abspath() usage: abspath <FILE>" 
}

print_usage() {
  stderr "usage:"
  stderr " \$ ${script} --list-implementations"
  stderr " \$ ${script} --gen-implementation IMPLEMENTATION DIRECTORY"
}

fatal_usage() {
  if (( "$#" != 0 )); then
    stderr "error:" "$@"
  fi
  print_usage
  exit 1
}

list_implementations() {
  make --no-print-directory -C "${project_dir}/src" print-available-implementations
}

gen_implementation() {
   if [ "${#}" -eq 2 ]; then

     # start by realpath them (useful to run make)
     implementation="$project_dir"/src/"${1}"
     directory="${2}"

     # test if IMPLEMENTATION directory exists
     if [ ! -d "${implementation}" ]; then
       fatal "implementation does not exist: ${implementation}"
     fi

    # test if libjade DIRECTORY exists
    if [ ! -d "${directory}" ]; then
       fatal "target directory does not exist: ${directory} "
    fi

    relative_implementation="$(realpath --relative-to="${project_dir}/src" "${implementation}")"
    make --no-print-directory -C "${project_dir}/src/" "${relative_implementation}/preprocess-inplace"

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
    make --no-print-directory -C "${project_dir}/src/" "${relative_implementation}/revert-preprocess-inplace"

    return 0
   else
    fatal_usage "$0 --gen-implementation: number of required arguments 3 : provided $#"
   fi
}

main() {
  cd "$(dirname "${0}")"
  project_dir="$(pwd -P)"
  cd "${project_dir}"

  local cmd; cmd="$1"; shift || fatal_usage "Please specify a command"
  case "${cmd}" in
    "--list-implementations")
      list_implementations "$@" ;;
    "--gen-implementation")
      gen_implementation "$@" ;;
    *)
      fatal_usage "Invalid command: ${cmd}" ;;
  esac
}

init() {
  set -e
  script="${0}"
  main "${@}"
}

init "${@}"
