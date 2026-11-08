import copy
import unittest
import interface_gate as g


def complete_shaped_inputs():
    final = {
        'schema': g.FINAL_SCHEMA, 'current_audit_sha256': g.CURRENT_SHA,
        'radius_scope': g.SCOPE, 'r_strict_interval': g.INTERVAL[:],
        'candidate_angle_unresolved_closed_boxes': 0,
        'Rstar_conditional_frontier_pending_subtrees': 0,
        'unrestricted_reduction_final_joint_acceptance': True,
        'full_catalog_complete': True, 'global_lower_bound_proved': True,
        'global_optimality_proved': True,
        'Rstar_conditional_frontier_families': [
            {'family_exhausted': True, 'pending_subtrees': 0, 'unresolved_terminal_subtrees': 0}],
    }
    current = {'schema': g.CURRENT_SCHEMA, 'r_strict_interval': g.INTERVAL[:],
               'radius_scope': g.SCOPE, 'files': {'original': 'sha'}}
    return final, current


class TestFailures(unittest.TestCase):
    def test_even_forged_success_cannot_be_accepted(self):
        f,c=complete_shaped_inputs()
        self.assertEqual(g.check(f,c), ['unimplemented fresh geometric/continuous-domain replay and global composition'])

    def test_missing_current(self):
        f,_=complete_shaped_inputs()
        self.assertIn('formal current unavailable', g.check(f,None))

    def test_old_or_changed_radius(self):
        f,c=complete_shaped_inputs()
        c['r_strict_interval']=['0.23','0.24']
        self.assertIn('current and final radius intervals differ', g.check(f,c))

    def test_scope_promotion(self):
        f,c=complete_shaped_inputs()
        f['radius_scope']='original-U'
        self.assertIn('wrong radius scope: same-root cannot be promoted to original U', g.check(f,c))

    def test_unpaid_root(self):
        f,c=complete_shaped_inputs()
        f['candidate_angle_unresolved_closed_boxes']=16
        self.assertIn('nonzero or missing unresolved field: candidate_angle_unresolved_closed_boxes',g.check(f,c))

    def test_unpaid_family_even_if_total_is_zero(self):
        f,c=complete_shaped_inputs()
        f['Rstar_conditional_frontier_families'][0]['pending_subtrees']=1
        self.assertIn('unclosed or malformed formal family',g.check(f,c))

    def test_bool_is_not_zero(self):
        f,c=complete_shaped_inputs()
        f['candidate_angle_unresolved_closed_boxes']=False
        self.assertIn('nonzero or missing unresolved field: candidate_angle_unresolved_closed_boxes',g.check(f,c))

    def test_global_flag_missing(self):
        f,c=complete_shaped_inputs()
        del f['global_lower_bound_proved']
        self.assertIn('missing global obligation: global_lower_bound_proved',g.check(f,c))


if __name__ == '__main__':
    unittest.main()
