/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */
#ifdef TEST
#include <stdio.h>
#include <stdlib.h>
#endif

unsigned long partition(unsigned int *a, unsigned long n)
{
   // assume n != 0

   // unsigned int pivot = a[0];
   unsigned long pivot_idx = 0; // stupid pivot choice for now

   for (unsigned long i = 1; i < n; i++) {
      if (a[i] < a[pivot_idx]) {
         unsigned int pivot = a[pivot_idx];
         a[pivot_idx] = a[i];
         pivot_idx++;
         a[i] = a[pivot_idx];
         a[pivot_idx] = pivot;
         // pivot = pivot; // hack to get AutoCorres to recognise "pivot" in the loop body
      }
   }

   return pivot_idx;
}

void quicksort(unsigned int *a, unsigned long n)
{
   if (n > 1) {
      unsigned long pivot_idx = partition(a, n);
      quicksort(a, pivot_idx);
      quicksort(a + pivot_idx + 1, n - pivot_idx - 1);
   }
}

#ifdef TEST

int main(void)
{
   unsigned int sz;
   scanf("%u", &sz);
   unsigned int *a = malloc(sz * sizeof(unsigned int));
   for (unsigned int i = 0; i < sz; i++) {
      scanf("%u", a+i);
   }

   quicksort(a, sz);

   for (unsigned int i = 0; i < sz; i++) {
      if (i) putchar(' ');
      printf("%u", a[i]);
   }
   printf("\n");

   return 0;
}

#endif
