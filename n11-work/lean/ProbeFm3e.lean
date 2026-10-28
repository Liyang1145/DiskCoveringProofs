import N11Formalization.Interval.Range
namespace N11Formalization
namespace RatInterval
#print inWindow
set_option trace.Meta.synthInstance true in
example (A : RatInterval) : Decidable (inWindow A 0) := inferInstance
end RatInterval
end N11Formalization
