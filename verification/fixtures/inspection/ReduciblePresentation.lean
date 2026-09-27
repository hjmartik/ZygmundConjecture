import PackagingFixtures.Contracts

namespace PackagingFixtures.ReduciblePresentation

def Alias (P : Prop) : Prop := P

theorem target : Alias True := True.intro

end PackagingFixtures.ReduciblePresentation
