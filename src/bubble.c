/*@ axiomatic Permut {
  @ predicate permut{L1,L2}(int *t1, int *t2, integer n);
  @ 	axiom permut_refl{L}:
  @ 		\forall int *t, integer n; permut{L,L}(t,t,n);
  @ 	axiom permut_sym{L1,L2}:
  @ 		\forall int *t1, *t2, integer n;
  @ 			permut{L1,L2}(t1,t2,n) ==> permut{L2,L1}(t2,t1,n);
  @ 	axiom permut_trans{L1,L2,L3}:
  @ 		\forall int *t1, *t2, *t3, integer n;
  @ 			permut{L1,L2}(t1,t2,n) && permut{L2,L3}(t2,t3,n)
  @ 			==> permut{L1,L3}(t1,t3,n);
  @ 	axiom permut_exchange{L1,L2}:
  @ 		\forall int *t1, *t2, integer i, j, n;
  @ 		swap{L1, L2}(t1, t2, i, j, n) ==> permut{L1,L2}(t1,t2,n);
  @ }
  @*/
/*@ predicate greatest(int *a, integer last) =
  @ 	\forall integer k;
  @		0 <= k < last ==> a[k] <= a[last];
  @
  @ predicate sorted(int *a, integer first, integer last) =
  @	\forall integer k;
  @		first < k < last ==> a[k - 1] <= a[k];
  @
  @ predicate swap{L1, L2}(int *a, int *b, integer i, integer j, integer n) =
  @	\forall integer k;
  @		\at(a[i], L1) == \at(b[j], L2) &&
  @		\at(a[j], L1) == \at(b[i], L2) &&
  @		(0 <= k < n && k != i && k != j ==> \at(a[k], L1) == \at(a[k], L2));
  @*/
/*@ requires n > 0;
  @ requires \valid(a + (0 .. n-1));
  @ 
  @ assigns a[0..n-1];
  @
  @ ensures sorted(a, 0, n);
  @ ensures permut{Pre, Here}(a, a, n);
  @*/
void bubble_sort(int *a, int n) {
	int i, j, tmp;
	/*@ loop invariant 0 <= i <= n - 1;
          @ loop invariant i > 0 ==> greatest(a, n - i);
	  @ loop invariant sorted(a, n - i - 1, n);
          @ loop invariant permut{Pre, Here}(a, a, n);
	  @ loop assigns i, j, tmp, a[0..n-1];
	  @ loop variant n - i;
	  @*/
	for (i = 0; i < n - 1; ++i) {
		/*@ loop invariant bound: 0 <= j < n - i;
		  @ loop invariant greatest(a, j);
		  @ loop invariant i > 0 ==> greatest (a, n - i);
		  @ loop invariant permut{Pre, Here}(a, a, n);
		  @
		  @ loop assigns j, tmp, a[0..n-i-1];
		  @ loop variant n - i - 1 - j;
		  @*/
		for (j = 0; j < n - i - 1; j++) {
			if (a[j] > a[j + 1]) {
				tmp = a[j];
				a[j] = a[j + 1];
				a[j + 1] = tmp;
				//@ assert swap{LoopCurrent, Here}(a, a, j, j + 1, n);
			}
		}
		//@ assert sorted(a, n - i - 1, n);
		//@ assert greatest(a, n - i - 1);
	}
}
