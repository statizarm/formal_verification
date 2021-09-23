/*@ inductive permut{L1, L2}(int *a, integer first, integer last) {
  @ 	case permut_refl{L}:
  @		\forall int *a, integer first, integer last;
  @			permut{L, L}(a, first, last);
  @	case permut_sym{L1, L2}:
  @		\forall int *a, integer first, integer last;
  @                     permut{L1, L2}(a, first, last) ==> permut{L2, L1}(a, first, last);
  @	case permut_trans{L1, L2, L3}:
  @		\forall int *a, integer first, integer last;
  @			permut{L1, L2}(a, first, last) && permut{L2, L3}(a, first, last) ==>
  @				permut{L1, L3}(a, first, last);
  @	case permut_swap{L1, L2}:
  @		\forall int *a, integer first, i, j, last;
  @			first <= i < last && first <= j < last && swap{L1, L2}(a, i, j) ==>
  @				permut{L1, L2}(a, first, last);
  @ }
  @*/

/*@ predicate swap{L1, L2}(int *a, integer i, integer j) =
  @	\at(a[i], L1) == \at(a[j], L2) &&
  @	\at(a[j], L1) == \at(a[i], L2) &&
  @	\forall integer k; k != i && k != j ==> \at(a[k], L1) == \at(a[k], L2);
  @
  @ predicate sorted(int *a, integer first, integer last) =
  @	\forall integer i;
  @		(first < i < last ==> a[i - 1] <= a[i]);
  @*/

/*@ requires \valid(a + i) && \valid(a + j);
  @ assigns a[i], a[j];
  @ ensures swap{Old, Here}(a, i, j);
  @*/
void swap(int *a, int i, int j) {
	int tmp = a[i];
	a[i] = a[j];
	a[j] = tmp;
}

/*@ requires n > 0;
  @ requires \valid(a + (0 .. n-1));
  @ 
  @ assigns a[0..n-1];
  @
  @ ensures sorted(a, 0, n);
  @ ensures permut{Old, Here}(a, 0, n);
  @*/
void bubble_sort(int *a, int n) {
	int i, j, tmp;
	//@ ghost int g_swap = 0;
	/*@ loop invariant 0 <= i <= n - 1;
	  @ loop invariant 0 <= g_swap <= 1;
	  @ loop invariant sorted(a, n - i - 1, n);
	  @ loop invariant 0 < i < n ==> \forall int k, l; 0 <= k <= n - i - 1 <= l < n ==> a[k] <= a[l];
	  @ loop invariant 0 < i < n ==> permut{Pre, Here}(a, 0, n);
	  @ loop assigns i, j, a[0..n-1];
	  @ loop variant n - i;
	  @*/
	for (i = 0; i < n - 1; ++i) {
		//@ ghost g_swap = 0;
		/*@ loop invariant bound: 0 <= j <= n - i - 1;
		  @ loop invariant 0 <= g_swap <= 1;
		  @ loop invariant 0 < j < n - i ==> \forall int k; 0 <= k < j ==> a[k] <= a[j];
		  @ loop invariant 0 < j < n - i ==> (g_swap == 1) ==> permut{Pre, Here}(a, 0, n);
		  @
		  @ loop assigns j, a[0..n-i-1];
		  @ loop variant n - i - 1 - j;
		  @*/
		for (j = 0; j < n - i - 1; j++) {
			if (a[j] > a[j + 1]) {
				//@ ghost g_swap = 1;
				swap(a, j, j + 1);
			}
		}
	}

	//@ assert sorted(a, n - i - 1, n);
}
