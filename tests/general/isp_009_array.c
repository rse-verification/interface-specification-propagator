/* run.config
OPT: -autoload-plugins -isp -isp-print
COMMENT: "Testing array data structures."
*/

int X[10];
int Y[2];

int first_4_sum() {
  return X[0] + X[1] + X[2] + X[3];
}

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(X+(0..3));
    requires \valid_read(&Y[1]);
    requires \valid(&Y[1]);
    requires X[0..2] == 1;
    requires X[3] == 2;
    ensures Y[1] == 5;
    assigns Y[1];
    */
void main() {
  Y[1] = first_4_sum();
}
