package io.cosmo.exo

object Play {

  case class Lens[S, A](get: S => A, set: (S, A) => S)
  case class Prism[S, A](get: S => Option[A], set: A => S)

  case class Mealey[F[_], S, I, O](transition: (S, I) => F[(S, O)]) { self =>
    def contramap[I0](f: I0 => I): Mealey[F, S, I0, O] = Mealey((s, i1) => transition(s, f(i1)))
    //def map[O1](f: O => O1): Mealey[F, S, I, O1] = Mealey((s, i) => transition(s, i).map { case (s1, o) => (s1, f(o)) })

//    def mapState[S0](f: Lens[S0, S]): Mealey[F, S0, I, O] =
//      Mealey((s0, i) => transition(f.get(s0), i).map { case (s1, o) => (f.set(s0, s1), o) })

//    def divide[K, J, Q](that: Mealey[F, K, J, Q]): Mealey[F, (S, K), Either[I, J], Either[O, Q]] =
//      Mealey((sk, ij) => ij match {
//        case Left(i) => self.transition(sk._1, i).map { case (s1, o) => ((s1, sk._2), Left(o)) }
//        case Right(j) => that.transition(sk._2, j).map { case (k1, q) => ((sk._1, k1), Right(q)) }
//      })

//    def divide[K, J, Q, S1, I1, O1](that: Mealey[F, K, J, Q])(implicit
//      s1: Lens[S1, S], s2: Lens[S1, K],
//      i1: Prism[I1, I], i2: Prism[I1, J],
//      o1: Prism[O1, O], o2: Prism[O1, Q]
//    ): Mealey[F, S1, I1, O1] =
//      Mealey((s1, ij) => ij match {
//        case Left(i) => self.transition(s1.get(s1), i).map { case (s2, o) => (s1.set(s1, s2), o1.set(o1, o)) }
//        case Right(j) => that.transition(s2.get(s1), j).map { case (k1, q) => (s1.set(s1, s2.set(s1, k1)), o2.set(o2, q)) }
//      })


  }

  object Mealey {
    def apply[F[_], S, I, O](transition: (S, I) => F[(S, O)]): Mealey[F, S, I, O] = new Mealey(transition)


  }

  sealed trait Client
  case class Person(id: Int, name: String) extends Client
  case class Company(id: Int, name: String, location: String) extends Client

  def iso: Client <=> Either[Person, Company] =
    Iso.unsafe(
      (c: Client) => c match {
        case p: Person => Left(p)
        case c: Company => Right(c)
      },
      (e: Either[Person, Company]) => e match {
        case Left(p) => p
        case Right(c) => c
      }
    )

}
