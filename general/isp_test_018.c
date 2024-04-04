/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing Lval index that evaluates to a singleton."
*/

int X;
int Y[10];

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires \valid_read(&Y[1]);
    requires \valid(&Y[1]);
    requires Y[0..9] == 0;
    requires X == 1;
    ensures Y[1] == 1;
    assigns Y[1];
    */
void main() {
    Y[X] = X;
}
