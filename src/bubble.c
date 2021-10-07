/*@ predicate greatest{L}(int *a, integer last) =
  @ 	\forall integer k;
  @		0 <= k < last ==> \at(a[k], L) <= \at(a[last], L);
  @
  @ predicate sorted{L}(int *a, integer first, integer last) =
  @	\forall integer k;
  @		first < k < last ==> \at(a[k - 1], L) <= \at(a[k], L);
  @*/
/*@ requires n > 0;
  @ requires \valid(a + (0 .. n-1));
  @ 
  @ assigns a[0..n-1];
  @
  @ ensures sorted(a, 0, n);
  @*/
void bubble_sort(int *a, int n) {
	int i, j, tmp;
	//@ assert sorted{Here}(a, n - 1, n);
	/*@ loop invariant 0 <= i <= n - 1;
	  @ loop invariant sorted(a, n - i - 1, n);
          @ loop invariant \forall integer k; n - i <= k < n ==> greatest(a, k);
	  @ loop assigns i, j, tmp, a[0..n-1];
	  @ loop variant n - i;
	  @*/
	for (i = 0; i < n - 1; ++i) {
		/*@ loop invariant bound: 0 <= j < n - i;
		  @ loop invariant greatest(a, j);
		  @ loop invariant \forall integer k; n - i <= k < n ==> greatest(a, k);
		  @ loop invariant i > 0 ==> a[n - i - 1] <= a[n - i];
		  @
		  @ loop assigns j, tmp, a[0..n-i-1];
		  @ loop variant n - i - 1 - j;
		  @*/
		for (j = 0; j < n - i - 1; j++) {
			if (a[j] > a[j + 1]) {
				tmp = a[j];
				a[j] = a[j + 1];
				a[j + 1] = tmp;
				//@ assert i > 0 ==> a[n - i - 1] <= a[n - i];
			}
		}
		//@ assert sorted(a, n - i - 1, n);
		//@ assert greatest(a, n - i - 1);
	}
}
