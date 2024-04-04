/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Test targetting a bug in the inference for contract for help functions that read from an array."
*/

int STATE[2];
int DB[2];

typedef enum { RPM = 0, SPEED = 1 } VEHICLE_STATE;

int read_state(int idx) {
  return STATE[idx];
}

int read_db(VEHICLE_STATE s) {
  return DB[s];
}

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(STATE+(0..1));
    requires \valid_read(DB+(0..1));
    requires STATE[0] ∈ (0..400);
    requires STATE[1] ∈ (0..9000);
    requires DB[RPM] ∈ (0..9000);
    requires DB[SPEED] ∈ (0..9000);
    assigns \nothing;
    */
void main() {
  read_state(1);
  read_state(0);
  read_db(RPM);
  read_db(SPEED);
}
