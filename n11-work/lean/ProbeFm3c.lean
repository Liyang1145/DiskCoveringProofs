import N11Formalization.Interval.Range
set_option trace.Meta.synthInstance true in
example (A : RatInterval) : Decidable (inWindow A 0) := inferInstance
namespace N11Formalization
namespace RatInterval
#check @inWindow
#check inWindow
end RatInterval
end N11Formalization
