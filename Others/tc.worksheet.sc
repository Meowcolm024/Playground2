trait Functor[F[_], A](self: F[A]):
    def map[B](f: A => B): F[B]

trait Pure[F[_]]:
    def pure[A](v: A): F[A]

trait Applicative[F[_], A](self: F[A]) extends Functor[F, A] with Pure[F]:
    def <&>[B](f: F[A => B]): F[B]

trait Monad[F[_], A](self: F[A]) extends Applicative[F, A]:
    def flatMap[B](f: A => F[B]): F[B]
    def >>= = flatMap

trait Empty[F[_]]:
    def empty[A]: F[A]

trait Alternative[F[_], A](self: F[A]) extends Applicative[F, A] with Empty[F]:
    def <|>(that: F[A]): F[A]

implicit class ListFunctor[A](self: List[A]) extends Functor(self):
    def map[B](f: A => B): List[B] = self.map(f)

implicit class ListApplicative[A](self: List[A]) extends ListFunctor(self) with Applicative(self):
    def pure[A](v: A): List[A] = List(v)
    def <&>[B](f: List[A => B]): List[B] = f.flatMap(self.map)

implicit class ListMonad[A](self: List[A]) extends ListApplicative(self) with Monad(self):
    def flatMap[B](f: A => List[B]): List[B] = self.flatMap(f)

implicit class ListAlternative[A](self: List[A]) extends ListApplicative(self) with Alternative(self):
    def empty[A]: List[A] = Nil
    def <|>(that: List[A]): List[A] = self ++ that

implicit def ListApp[A]: Applicative[List, A] = ListApplicative(Nil)
implicit def ListAlt[A]: Alternative[List, A] = ListAlternative(Nil)

def guard[F[_]](p: Boolean)(implicit A: Alternative[F, ?]): F[Unit] =
    if p then A.pure(()) else A.empty

val ha =
    for
        i <- 1 to 10
        _ <- guard(i % 2 == 0)
    yield
        i

def f[F[_]](s: Int)(implicit A: Applicative[F, Int]) = A.pure(s)

f(1)
