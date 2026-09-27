import PackagingFixtures.Contracts

namespace PackagingFixtures.ExtraAssumption

theorem target : ∀ n : Nat, n = 0 → n = n := fun _ _ => rfl

end PackagingFixtures.ExtraAssumption
