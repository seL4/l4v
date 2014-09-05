theory struct2
imports "../../AutoCorres"
begin

install_C_file "struct2.c"

autocorres [keep_going] "struct2.c"

end
