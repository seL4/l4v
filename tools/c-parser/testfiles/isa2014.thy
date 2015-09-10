theory isa2014
  imports "../CTranslation"
begin

  install_C_file "isa2014.c"
  
  print_locale isa2014_global_addresses
  
context isa2014
begin

  thm f_body_def
  thm ff_body_def
  
end (* context *)  
  
end
