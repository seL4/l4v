(*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory static_assert
imports "CParser.CTranslation"
begin

external_file "static_assert.c"
install_C_file "static_assert.c"

context static_assert
begin

end
end
