/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing enum data structures and typedef."
*/

typedef enum { EN1, EN2, EN3, EN4, NUM_ENS } SIGNAL;

int X[NUM_ENS];

int first_3_sum() {
  return X[EN1] + X[EN2] + X[EN3];
}

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(X+(0..3));
    requires \valid(&X[3]);
    requires X[0..1] == 1;
    requires X[EN3] ∈ {1,2,3,4,5};
    assigns X[3];
    */
void main() {
  X[3] = first_3_sum();
}
