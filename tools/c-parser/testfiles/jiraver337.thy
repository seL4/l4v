theory jiraver337
  imports "../CTranslation"
begin


  declare [[cpp_path=""]]
  install_C_file "jiraver337.c"

  context jiraver337
  begin
    thm f_body_def
  end (* context *)
  
end
