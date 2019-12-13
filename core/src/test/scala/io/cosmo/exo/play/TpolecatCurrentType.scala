package io.cosmo.exo.play

object TpolecatCurrentType {

  /**
   * from tpolecat's blog: https://tpolecat.github.io/2015/04/29/f-bounds.html
   */

  locally { // pets first try
    trait Pet {
      def name: String
      def renamed(newName: String): Pet
    }

    case class Fish(name: String, age: Int) extends Pet {
      def renamed(newName: String): Fish = copy(name = newName)
    }
    val a = Fish("Jimmy", 2)
    val b = a.renamed("Bob")

    case class Kitty(name: String, color: Int) extends Pet {
      def renamed(newName: String): Fish = new Fish(newName, 42) // oops
    }

    // doesn't work
    //def esquire[A <: Pet](a: A): A = a.renamed(a.name + ", Esq.")
  }

  locally {  // pets second try: F-bounded types
    trait Pet[A <: Pet[A]] {
      def name: String
      def renamed(newName: String): A // note this return type
    }
    case class Fish(name: String, age: Int) extends Pet[Fish] { // note the type argument
      def renamed(newName: String) = copy(name = newName)
    }
    val a = Fish("Jimmy", 2)
    val b = a.renamed("Bob")

    def esquire[A <: Pet[A]](a: A): A = a.renamed(a.name + ", Esq.")
    esquire(a)

    // but sadly I can lye when subtyping: Here a kitty renames into a fish!
    case class Kitty(name: String, color: Int) extends Pet[Fish] { // oops
      def renamed(newName: String): Fish = new Fish(newName, 42)
    }
  }

  locally { // pets third take: Typeclasses
    trait Pet[A] {
      def name(a: A): String
      def renamed(a: A, newName: String): A
    }
    implicit class PetOps[A](a: A)(implicit ev: Pet[A]) {
      def name = ev.name(a)
      def renamed(newName: String): A = ev.renamed(a, newName)
    }

    case class Fish(name: String, age: Int)
    object Fish {
      implicit val FishPet = new Pet[Fish] {
        def name(a: Fish) = a.name
        def renamed(a: Fish, newName: String) = a.copy(name = newName)
      }
    }
    Fish("Bob", 42).renamed("Steve")

    case class Kitty(name: String, color: Int)
    object Kitty {
      implicit object KittyPet extends Pet[Kitty] {
        def name(a: Kitty) = a.name
        def renamed(a: Kitty, newName: String) = a.copy(name = newName)
      }
    }

    def esquire[A: Pet](a: A): A = a.renamed(a.name + ", Esq.")

    val bob  = Fish("Bob", 12)
    val thor = Kitty("Thor", 555)

    trait ∃[F[_]] {
      type A
      val a: A
      val fa: F[A]
      override def toString = a.toString
    }

    object ∃ {
      def apply[F[_], A0](a0: A0)(implicit ev: F[A0]): ∃[F] =
        new ∃[F] {
          type A = A0
          val a = a0
          val fa = ev
        }
    }
    List[∃[Pet]](∃(bob), ∃(thor)).map(e => ∃(esquire(e.a)(e.fa))(e.fa))
    // res15: List[∃[Pet]] = List(Fish(Bob, Esq.,12), Kitty(Thor, Esq.,java.awt.Color[r=255,g=200,b=0]))


    import shapeless._

    object polyEsq extends Poly1 {
      implicit def default[A: Pet] = at[A](esquire(_))
    }

    (bob :: thor :: HNil) map polyEsq // output reformatted for readability
    // res11: Fish :: Kitty :: HNil = Fish(Bob, Esq.,12) ::  Kitty(Thor, Esq.,555 :: HNil
  }

}
