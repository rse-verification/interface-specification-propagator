/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Function arguments with unused arguments in if 
          branches, non-pointer. Failing because of over approximation!"
*/

int X;

int increment(int x, int y) {
  if (y == 1) {
    x = 2;
    x += 1;
  }
  return x;
}

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires X \in {1,2};
    ensures \result \in {2,3};
    assigns \nothing;
    */
int main() {
  int temp = increment(X, X);
  return temp;
}
