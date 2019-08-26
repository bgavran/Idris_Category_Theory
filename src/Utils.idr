module Utils

public export
cong2 : (f : t -> u -> v) -> a = b -> c = d -> f a c = f b d
cong2 _ Refl Refl = Refl

public export
cong3 : (f : t -> u -> v -> w) -> a = b -> c = d -> e = g -> f a c e = f b d g
cong3 _ Refl Refl Refl = Refl

public export
cong4 : (f : t -> u -> v -> w -> y)
  -> a = b
  -> c = d
  -> e = g
  -> h = j
  -> f a c e h = f b d g j
cong4 _ Refl Refl Refl Refl = Refl

public export
funext : {f, g : a -> b}
  -> ((x : a) -> f x = g x)
  -> f = g
funext e = believe_me ()
