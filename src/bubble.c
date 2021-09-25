/*@ axiomatic COUNT {
  @ 	logic integer count{L}(int *a, int num, integer n);
  @	axiom count_empty{L}:
  @		\forall int *a, num, integer n;
  @			n == 0 ==> count{L}(a, num, n) == 0;
  @	axiom count_matched_last{L}:
  @		\forall int *a, num, integer n;
  @			\at(a[n - 1], L) == num ==> count{L}(a, num, n) == count{L}(a, num, n - 1) + 1;
  @	axiom count_unmatched_last{L}:
  @		\forall int *a, num, integer n;
  @			\at(a[n - 1], L) != num ==> count{L}(a, num, n) == count{L}(a, num, n - 1);
  @ }
  @*/
/*@ predicate sorted{L}(int *a, integer first, integer last) =
  @	\forall integer i;
  @		first < i < last ==> \at(a[i - 1], L) <= \at(a[i], L);
  @*/
/*@ predicate greatest{L}(int *a, integer last) =
  @ 	\forall integer i;
  @		0 <= i < last ==> \at(a[i], L) <= \at(a[i], L);
  @*/
/*@ axiomatic MULTISET_EQUAL {
  @ 	logic boolean mequal{L1, L2}(int *a, integer n);
  @	axiom mequal_refl{L}:
  @		\forall int *a, integer n;
  @			mequal{L, L}(a, n) == \true;
  @	axiom mequal_sym{L1, L2}:
  @		\forall int *a, integer n;
  @			mequal{L1, L2}(a, n) ==> mequal{L2, L1}(a, n);
  @	axiom mequal_trans{L1, L2, L3}:
  @		\forall int *a, integer n;
  @			mequal{L1, L2}(a, n) && mequal{L2, L3}(a, n) ==> mequal{L1, L3}(a, n);
  @	axiom mequal{L1, L2}:
  @		\forall int *a, i, n;
  @			0 <= i < n ==>
  @			mequal{L1, L2}(a, n) == (count{L1}(a, \at(a[i], L2), n) == count{L2}(a, \at(a[i], L2), n));
  @ }
  @*/

/*@ requires n > 0;
  @ requires \valid(a + (0 .. n-1));
  @ 
  @ assigns a[0..n-1];
  @
  @ ensures sorted{Here}(a, 0, n);
  @ ensures mequal{Old, Here}(a, n);
  @*/
void bubble_sort(int *a, int n) {
	int i, j, tmp;
	/*@ loop invariant 0 <= i <= n - 1;
	  @ loop invariant sorted{Here}(a, n - i - 1, n);
	  @ loop invariant mequal{Pre, Here}(a, n);
	  @ loop assigns i, j, tmp, a[0..n-1];
	  @ loop variant n - i;
	  @*/
	for (i = 0; i < n - 1; ++i) {
		/*@ loop invariant bound: 0 <= j < n - i;
		  @ loop invariant greatest{Here}(a, j);
		  @ loop invariant mequal{Pre, Here}(a, n);
		  @
		  @ loop assigns j, tmp, a[0..n-i-1];
		  @ loop variant n - i - 1 - j;
		  @*/
		for (j = 0; j < n - i - 1; j++) {
			if (a[j] > a[j + 1]) {
				tmp = a[j];
				a[j] = a[j + 1];
				a[j + 1] = tmp;
			}
		}
	}

	//@ assert sorted(a, n - i - 1, n);
}
