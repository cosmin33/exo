package io.cosmo.exo.play

object ShapelessTaggedPlay {

  import shapeless.tag.@@
  import shapeless.tag

  trait ProfileIdTag
  trait ArenaIdTag
  trait BracketIdTag

  type ProfileId = String @@ ProfileIdTag
  type ArenaId   = String @@ ArenaIdTag
  type BracketId = String @@ BracketIdTag

  case class Arena(
    id: ArenaId, // <- tagged type
    name: String
  )

  case class Bracket(
    id: BracketId, // <- tagged type
    arenaId: ArenaId // <- tagged type
  )

  case class PlayerProfile(
    id: ProfileId, // <- tagged type
    bracketMapping: Map[ArenaId, BracketId] // <- tagged types
  ) {
    def changeBracket(arena: Arena, bracket: Bracket): PlayerProfile = {
      this.copy(bracketMapping = this.bracketMapping + (arena.id -> bracket.id))
    }
  }

  val profileId: ProfileId = tag[ProfileIdTag][String]("profileId")
  val arenaId: ArenaId     = tag[ArenaIdTag][String]("thePit")
  val bracketId: BracketId = tag[BracketIdTag][String]("bracket1")

}
