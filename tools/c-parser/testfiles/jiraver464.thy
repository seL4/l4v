theory jiraver464
  imports "../CTranslation"
begin 

ML {* 
val sup_name = @{const_name "sup"}
val union_t = @{term "A Un B"} 
val inter_t = @{term "A \<inter> B"}
*}

install_C_file "jiraver464.c"

thm SmallStep.step.cases

print_locale f_spec
context f_spec
begin
  thm f_spec_def
end

context jiraver464
begin
  thm f_body_def
end

end 