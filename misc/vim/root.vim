"
" Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
"
" SPDX-License-Identifier: BSD-2-Clause
"

" Vim syntax highlighting configuration for Isabelle ROOT files. Based on
" sections 2.1, 2.2 of the Isabelle System Manual.

" From section 2.1:
syn keyword RootKeyword chapter description document_files files in options
    \ session theories global_theories

" From ~~/etc/options
syn keyword RootOption browser_info document document_output document_variants
    \ document_graph thy_output_display thy_output_break thy_output_quotes
    \ thy_output_indent thy_output_source thy_output_modes show_types
    \ show_sorts show_question_marks show_consts show_main_goal goals_limit
    \ names_long names_short names_unique eta_contract pretty_margin print_mode
    \ threads threads_trace parallel_print parallel_proofs
    \ parallel_subproofs_threshold quick_and_dirty skip_proofs condition timing
    \ timeout process_output_limit use_stale_heaps ML_exception_trace
    \ editor_load_delay editor_input_delay editor_output_delay
    \ editor_prune_delay editor_update_delay editor_reparse_limit
    \ editor_tracing_messages editor_chart_delay editor_continuous_checking
    \ editor_execution_delay editor_syslog_limit find_theorems_limit
    \ find_theorems_tactic_limit completion_limit

syn region RootComment start="(\*" end="\*)"
syn region RootDescription start="{\*" end="\*}"
syn region RootString start='"' end='"'
syn match RootNumber "\m[0-9]\+"
syn match RootBool "\(true\|false\)"
syn keyword RootFormat pdf

" Enable syntax-based folding of sessions.
syn region RootSessionFold fold keepend transparent
    \ start="\(\<session\>\)\@<=" end="\ze\(\s*\n\)\+\(\S\|\%$\)"

hi def link RootKeyword Statement
hi def link RootOption Type
hi def link RootComment Comment
hi def link RootDescription Comment
hi def link RootString Constant
hi def link RootNumber Constant
hi def link RootBool Constant
hi def link RootFormat Constant
