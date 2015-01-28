theory jiraver432
  imports "../CTranslation"
begin

install_C_file "jiraver432.c"

thm AnonStruct1'_size
thm AnonStruct2'_size

context jiraver432
begin
  thm f_body_def
end (* context *)

end

