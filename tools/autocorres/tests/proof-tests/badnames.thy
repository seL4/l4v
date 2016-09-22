theory badnames
imports "../../AutoCorres"
begin

declare [[allow_underscore_idents = true]]

install_C_file "badnames.c"

autocorres "badnames.c"

end
