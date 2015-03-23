theory jiraver440
  imports "../CTranslation"
begin

  install_C_file "jiraver440.c"

  context jiraver440
  begin

  thm f_body_def
  thm g_body_def
  
  lemma "f_body = g_body"
  by (simp add: f_body_def g_body_def)
  
  
  end

end
