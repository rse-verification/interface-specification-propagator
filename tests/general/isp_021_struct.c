/* run.config
OPT: -autoload-plugins -isp -isp-print
COMMENT: "Testing struct."
*/

typedef struct {
  int a;
  int b;
  int c;
} MY_STRUCT;

int X;
MY_STRUCT Y;

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires \valid_read(&Y.a);
    requires \valid_read(&Y.b);
    requires \valid_read(&Y.c);
    requires \valid(&Y.a);
    requires \valid(&Y.b);
    requires \valid(&Y.c);
    requires X == 1;
    ensures Y.a == 1 && Y.b == 2 && Y.c == 3;
    assigns Y.a, Y.b, Y.c;
    */
void main() {
  Y.a = X;
  Y.b = 2 * X;
  Y.c = 3 * X;
}
