theory jiraver443a
  imports "../CTranslation"
begin

  install_C_file "jiraver443a.c"
  
context jiraver443a
begin

term "symbol_table"
thm get_body_def

end (* context *)

end
