theory jiraver464
  imports "../CTranslation"
begin

(* declare [[calculate_modifies_proofs=false]] *)
install_C_file "jiraver464.c"

print_locale f_spec
context f_spec
begin
  thm f_spec_def
end

context jiraver464
begin
  thm f_body_def
  thm f_modifies

thm clz_body_def
thm clz_modifies

thm clz_body_def
thm halt_body_def

end

end
