theory jiraver426
  imports "../CTranslation"
begin

install_C_file "jiraver426.c"

context jiraver426
begin

thm f_body_def
thm myexit_body_def

end (* context *)

end

