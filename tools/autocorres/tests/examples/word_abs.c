/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/* Regression test for VER-366 */
unsigned ver366(unsigned x) {
  if (x == 0) return 0;
  else        return x - 1;
}

/* All arithmetic operators */
unsigned U_add_U(unsigned a, unsigned b) { return a + b; }
unsigned U_sub_U(unsigned a, unsigned b) { return a - b; }
unsigned U_mul_U(unsigned a, unsigned b) { return a * b; }
unsigned U_div_U(unsigned a, unsigned b) { return a / b; }
unsigned U_mod_U(unsigned a, unsigned b) { return a % b; }
unsigned neg_U(unsigned a) { return -a; }

int S_add_S(int a, int b) { return a + b; }
int S_sub_S(int a, int b) { return a - b; }
int S_mul_S(int a, int b) { return a * b; }
int S_div_S(int a, int b) { return a / b; }
int S_mod_S(int a, int b) { return a % b; }
int neg_S(int a) { return -a; }

/* All bitwise operators */
unsigned U_and_U(unsigned a, unsigned b) { return a & b; }
unsigned U_or_U (unsigned a, unsigned b) { return a | b; }
unsigned U_xor_U(unsigned a, unsigned b) { return a ^ b; }
unsigned not_U(unsigned a) { return ~a; }

int S_and_S(int a, int b) { return a & b; }
int S_or_S (int a, int b) { return a | b; }
int S_xor_S(int a, int b) { return a ^ b; }
int not_S(int a) { return ~a; }

/* Shifts are more complicated, because the operands may have
 * different widths/signedness and there is no implicit promotion.
 *
 * This also entails a combinatorial explosion of cases depending on
 * whether signed/unsigned word abs is enabled for a given function. */

unsigned U_shiftl_U_no_abs(unsigned a, unsigned b) { return a << b; }
unsigned U_shiftr_U_no_abs(unsigned a, unsigned b) { return a >> b; }
unsigned U_shiftl_S_no_abs(unsigned a, int b) { return a << b; }
unsigned U_shiftr_S_no_abs(unsigned a, int b) { return a >> b; }
int S_shiftl_U_no_abs(int a, unsigned b) { return a << b; }
int S_shiftr_U_no_abs(int a, unsigned b) { return a >> b; }
int S_shiftl_S_no_abs(int a, int b) { return a << b; }
int S_shiftr_S_no_abs(int a, int b) { return a >> b; }

unsigned U_shiftl_U_abs_U(unsigned a, unsigned b) { return a << b; }
unsigned U_shiftr_U_abs_U(unsigned a, unsigned b) { return a >> b; }
unsigned U_shiftl_S_abs_U(unsigned a, int b) { return a << b; }
unsigned U_shiftr_S_abs_U(unsigned a, int b) { return a >> b; }
int S_shiftl_U_abs_U(int a, unsigned b) { return a << b; }
int S_shiftr_U_abs_U(int a, unsigned b) { return a >> b; }
int S_shiftl_S_abs_U(int a, int b) { return a << b; }
int S_shiftr_S_abs_U(int a, int b) { return a >> b; }

unsigned U_shiftl_U_abs_S(unsigned a, unsigned b) { return a << b; }
unsigned U_shiftr_U_abs_S(unsigned a, unsigned b) { return a >> b; }
unsigned U_shiftl_S_abs_S(unsigned a, int b) { return a << b; }
unsigned U_shiftr_S_abs_S(unsigned a, int b) { return a >> b; }
int S_shiftl_U_abs_S(int a, unsigned b) { return a << b; }
int S_shiftr_U_abs_S(int a, unsigned b) { return a >> b; }
int S_shiftl_S_abs_S(int a, int b) { return a << b; }
int S_shiftr_S_abs_S(int a, int b) { return a >> b; }

unsigned U_shiftl_U_abs_US(unsigned a, unsigned b) { return a << b; }
unsigned U_shiftr_U_abs_US(unsigned a, unsigned b) { return a >> b; }
unsigned U_shiftl_S_abs_US(unsigned a, int b) { return a << b; }
unsigned U_shiftr_S_abs_US(unsigned a, int b) { return a >> b; }
int S_shiftl_U_abs_US(int a, unsigned b) { return a << b; }
int S_shiftr_U_abs_US(int a, unsigned b) { return a >> b; }
int S_shiftl_S_abs_US(int a, int b) { return a << b; }
int S_shiftr_S_abs_US(int a, int b) { return a >> b; }
