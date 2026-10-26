/* Expose CaDiCaL's own unit propagation to cubical's C.
 *
 * Solver::propagate() propagates the current IPASIR assumptions and
 * Solver::implied() hands back the resulting trail, so we do not need our
 * own watched-literal propagator -- and CaDiCaL's version is strictly
 * stronger, since it propagates over everything it has learned across all
 * previous nodes, not just the original CNF.
 *
 * ipasir_init() returns ccadical.cpp's 'Wrapper', whose first data member
 * is the Solver pointer.  We re-declare a struct with the same bases in the
 * same order so that member sits at the same offset; cubical_fixed() lets
 * the caller verify that against ccadical_fixed() at startup.
 */
#include "cadical.hpp"
#include <vector>

namespace CaDiCaL {
struct ShimWrapper : Learner, Terminator {
  Solver *solver;
  bool terminate () { return false; }
  bool learning (int) { return false; }
  void learn (int) {}
};
} // namespace CaDiCaL

static CaDiCaL::Solver *sol (void *w) {
  return ((CaDiCaL::ShimWrapper *) w)->solver;
}

extern "C" {

/* 0 unknown, 10 satisfied, 20 refuted by propagation alone */
int cubical_propagate (void *w) { return sol (w)->propagate (); }

/* fills `out` with the implied trail, returns how many were WRITTEN -- never
 * more than `cap`, so the caller can walk the result without reading past the
 * buffer it handed us.  The trail cannot exceed one literal per variable, so a
 * cap of nvars+1 never actually truncates; returning the clamped count is so
 * that it stays safe if that ever stops holding. */
int cubical_implied (void *w, int *out, int cap) {
  std::vector<int> v;
  sol (w)->implied (v);
  int n = (int) v.size ();
  if (n > cap) n = cap;
  for (int i = 0; i < n; i++) out[i] = v[i];
  return n;
}

/* only so the caller can check the Wrapper layout assumption.  vars() is the
 * useful one: it returns a value the caller knows independently (the formula's
 * variable count), so a wrong offset cannot slip through by returning the same
 * zero on both sides, which is all fixed() can do before the first solve. */
int cubical_vars (void *w) { return sol (w)->vars (); }
int cubical_fixed (void *w, int lit) { return sol (w)->fixed (lit); }

/* Solver::set, with the answer kept.
 *
 * ccadical_set_option throws it away, so through the C API an option CaDiCaL
 * does not have -- a typo, or a name from another release -- is accepted in
 * silence and does nothing.  Reading the value back afterwards does not catch
 * it either: get_option returns 0 for a name it does not know, so
 * "--opt luckyy=0" reads back as the 0 that was asked for and looks applied.
 * A whole benchmark can then run believing it disabled something.
 *
 * set() returns false both for an unknown name and for a value outside the
 * option's range, which are the two things worth refusing, and distinguishes
 * neither -- the caller reports both and names the two possibilities. */
int cubical_set_option (void *w, const char *name, int val) {
  return sol (w)->set (name, val) ? 1 : 0;
}
}
