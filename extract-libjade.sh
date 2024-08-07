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
  local source target

  source="$project_dir"/src/"${1}"; shift || fatal_usage "Please specify an implementation!"
  target="${1}"; shift || fatal_usage "Please specify a target directory"
  (( "$#" == 0 )) || fatal_usage "Spurious arguments"

  [ -d "${source}" ] || fatal_usage "Implementation does not exist: ${source}"
  [ -d "${target}" ] || fatal_usage "target directory does not exist: ${target}"

  local relative_source
  relative_source="$(realpath --relative-to="${project_dir}/src" "${source}")"

  # Apply preprocessing
  make --no-print-directory -C "${project_dir}/src/" "${relative_source}/preprocess-inplace"

  # TODO: This is not robust against newlines in file names
  local jasmine_files
  mapfile -t jasmine_files < <(find "${source}" -type f -name '*.jazz')

  # Copy jasmine files to output directory
  local file
  for file in "${jasmine_files[@]}"; do
    echo >&2 "JASMINE FILE ${file}"
    cp "${file}" -t "${target}"
  done

  # setup the Makefile
  {
    # TODO: This will fail to properly deal with spaces for lack of quoting
    # https://stackoverflow.com/questions/23330243/gnu-makefile-how-to-and-when-to-quote-strings

    echo -n "SRCS := "
    for file in "${jasmine_files[@]}"; do
      echo -n "$(basename "${file}")"
    done
    echo ""

    # NOTE: the following line will need change (or be deleted) once multi-repo libjade is stable
    echo "include ../../../../Makefile.common"
  } > "${target}/Makefile"

  # NOTE: the following command will change once there is a PR in libjade to move api.h files out of include/ directories
  mkdir -p "${target}/include"
  cp "${source}/include/api.h" "${target}/include/api.h"

  # restore source state
  make --no-print-directory -C "${project_dir}/src/" "${relative_source}/revert-preprocess-inplace"
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
