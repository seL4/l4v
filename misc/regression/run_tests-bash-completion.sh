# Copyright 2025 Proofcraft Pty Ltd
#
# SPDX-License-Identifier: BSD-2-Clause
#
# bash completion for run_tests
# source this file to use: . ./run_tests-bash-completion.sh
#

_run_tests_sessions() {
  # $1 is run_tests
  # use -L to remove sessions that are excluded by L4V_ARCH selection
  case "$L4V_ARCH" in
    ""|"ARM")
      # prints additional line about setting L4V_ARCH_IS_ARM
      "$1" -L | tail -n +3
      ;;
    "ARM_HYP"|"X64"|"RISCV64"|"AARCH64")
      "$1" -L | tail -n +2
      ;;
  esac
}

_run_tests_completion() {
  local all_opts="--l4v-arches --l4v-arch-all -h --help -d --directory \
                  --brief -f --fail-fast -j --jobs -l --list -L --dry-run \
                  --no-dependencies -x --exclude -r --remove -v --verbose \
                  --dot --junit-report --stuck-timeout --scale-timeouts \
                  --no-timeouts --grace-period"
  local cur="${COMP_WORDS[$COMP_CWORD]}"
  local L4V_ARCHES="ARM ARM_HYP X64 RISCV64 AARCH64"

  if [[ ${cur} == -* ]]; then
    COMPREPLY=($(compgen -W "${all_opts}" -- "${cur}"))
  else
    local prev=""
    if [[ ${COMP_CWORD} -gt 1 ]]; then
      prev="${COMP_WORDS[$COMP_CWORD-1]}"
    fi
    if [[ "${prev}" == "-d" ]] || [[ "${prev}" == "--directory" ]]; then
      COMPREPLY=($(compgen -d -- "${cur}"))
    elif [[ "${prev}" == "--junit-report" ]]; then
      COMPREPLY=($(compgen -f -- "${cur}"))
    elif [[ "${prev}" == "--l4v-arches" ]]; then
      # List of architectures; comma separation not nicely supported.
      # For bash, the entire comma-separated list is one argument. If we only
      # return the last argument for completion, the prefix will disapplear,
      # because bash replaces the entire argument with the completion.
      # We can present the last element as input, but we must return the
      # entire list as output.
      local PREFIX="${cur%,*}"
      local POSTFIX="${cur##*,}"
      local ARCHES=($(compgen -W "${L4V_ARCHES}" -- "${POSTFIX}"))
      if [[ "${POSTFIX}" == "${cur}" ]]; then
        COMPREPLY=("${ARCHES[@]}")
      else
        COMPREPLY=()
        for arch in ${ARCHES[@]}; do
          COMPREPLY+=("${PREFIX},${arch}")
        done
      fi
    else
      # arguement $1 is <path>/run_tests
      COMPREPLY=($(compgen -W "$(_run_tests_sessions $1)" -- "${cur}"))
    fi
  fi
}

complete -F _run_tests_completion run_tests
