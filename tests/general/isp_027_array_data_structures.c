/* run.config
OPT: -autoload-plugins -isp -isp-print
COMMENT: "Testing array data structures."
*/

int DB[5];

void help_function(int idx) {
  DB[idx] = 3;
}
/*@ behavior interface_spec:
      assumes \true;
      requires \valid_read(&DB[1]);
      requires \valid(&DB[1]);
      ensures DB[1] ≡ 3;
      assigns DB[1];
*/
void main() {
  help_function(1);
}
