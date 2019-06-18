extern crate num_bigint as bigint;

extern crate num_integer as integer;
extern crate num_rational as rational;
use integer::Roots;

use std::fmt;

use core::ops::{Add, Div, Mul, Neg, Sub};

use core::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};

use std::rc::Rc;

use Constructible::*;

#[derive(Debug, Clone)]
pub enum Constructible {
    Rat(rational::Rational),
    Con {
        a: Rc<Constructible>,
        b: Rc<Constructible>,
        r: Rc<Constructible>,
    },
}

fn eq_rep(x: &Constructible, y: &Constructible) -> bool {
    //TODO improve performance from 3^n to 2^n
    match (x, y) {
        (Rat(x), Rat(y)) => x == y,
        (Rat(_), Con { .. }) | (Con { .. }, Rat(_)) => false,
        (
            Con { a, b, r },
            Con {
                a: a2,
                b: b2,
                r: r2,
            },
        ) => eq_rep(a, a2) && eq_rep(b, b2) && eq_rep(r, r2),
    }
}

impl Constructible {
    fn join(&self, other: &Self) -> Constructible {
        //output==self but other.strict_subfield(self) or other.same_field(self)
        match self {
            Rat(_) => match other {
                Rat(_) => self.clone(),
                Con { a: _, b: _, r } => Con {
                    a: Rc::new(self.join(r)),
                    b: Rc::new(Constructible::from_integer(0).join(r)),
                    r: Rc::clone(r),
                },
            },
            Con { a, b, r } => {
                let a = a.join(other);
                let b = b.join(other);
                let r = r.join(other);
                &a + &(&b * &(r.sqrt()))
            }

        }
    }
    fn inverse(&self) -> Constructible {
        match self {
            Rat(x) => Rat(rational::Rational::from_integer(1) / x),
            Con {
                ref a,
                ref b,
                ref r,
            } => {
                let a = &**a;
                let b = &**b;
                let d = &(a * a) - &(&(b * b) * r);
                Con {
                    a: Rc::new(a / &d),
                    b: Rc::new(&(-b) / &d),
                    r: Rc::clone(r),
                }
            }
        }
    }
    fn is_zero(&self) -> bool {
        match self {
            Rat(x) => x == &rational::Rational::from_integer(0),
            Con { a, b, r: _ } => a.is_zero() && b.is_zero(),
        }
    }
    fn same_field(&self, other: &Self) -> bool {
        match (self, other) {
            (Rat(_), Rat(_)) => true,
            (Rat(_), Con { .. }) | (Con { .. }, Rat(_)) => false,
            (Con { a: _, b: _, r }, Con { a: _, b: _, r: r2 }) => eq_rep(r, r2),
        }
    }
    fn strict_subfield(&self, other: &Self) -> bool {
        match other {
            Rat(_) => false,
            Con { a: _, b: _, r: r2 } => match self {
                Rat(_) => true,
                Con { a: _, b: _, r: _ } => self.same_field(r2) || self.strict_subfield(r2),
            },
        }
    }
    fn try_sqrt(&self) -> Option<Constructible> {
        match self {
            Rat(x) => {
                if x < &rational::Rational::from_integer(0) {
                    None
                } else {
                    let &n = x.numer();
                    let &d = x.denom();
                    let (rn, rd) = (n.sqrt(), d.sqrt());
                    if rn * rn == n && rd * rd == d {
                        Some(Rat(rational::Rational::new(rn, rd)))
                    } else {
                        None
                    }
                }
            }
            Con { a, b, r } => {
                let a = &**a;
                let b = &**b;
                match (&(a * a) - &(&(b * b) * r)).try_sqrt() {
                    Some(ref n) => {
                        if let Some(u) = (&(n + a) / &(Constructible::from_integer(2))).try_sqrt() {
                            Some(Con {
                                a: Rc::new(u.clone()),
                                b: Rc::new(b / &(&(Constructible::from_integer(2)) * &u)),
                                r: Rc::clone(r),
                            })
                        } else if let Some(v) =
                            (&(n + a) / &(&(Constructible::from_integer(2)) * &r)).try_sqrt()
                        {
                            Some(Con {
                                a: Rc::new(b / &(&(Constructible::from_integer(2)) * &v)),
                                b: Rc::new(v),
                                r: Rc::clone(r),
                            })
                        } else {
                            None
                        }
                    }
                    None => None,
                }
            }
        }
    }
    pub fn sqrt(&self) -> Constructible {
        assert!(self >= &(self - self), "sqrt called with negative argument");
        match self.try_sqrt() {
            Some(x) => x,
            None => Con {
                a: Rc::new(Constructible::from_integer(0).join(self)),
                b: Rc::new(Constructible::from_integer(1).join(self)),
                r: Rc::new(self.clone()),
            },
        }
    }
    pub fn from_rational(x: rational::Rational) -> Constructible {
        Rat(x)
    }
    pub fn from_integer(x: isize) -> Constructible {
        Rat(rational::Rational::from_integer(x))
    }
    pub fn to_float(&self) -> f32{
        match self {
            Rat(x) => *x.numer() as f32 / *x.denom() as f32,
            Con{a,b,r} => a.to_float()+b.to_float()*r.to_float().sqrt(),
        }
    }
}

impl fmt::Display for Constructible{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self{
            Rat(x)=> write!(f,"{}",x),
            Con{a,b,r}=> {
                if **b == Constructible::from_integer(0) {
                    write!(f,"{}",a)
                }else if **b == Constructible::from_integer(1) {
                    if **a == Constructible::from_integer(0) {
                        write!(f,"sqrt({})",r)
                    }else {
                        write!(f,"{}+sqrt({})",a,r)
                    }
                }else {
                    if **a != Constructible::from_integer(0) {
                        write!(f,"{}+",a)?
                    }
                    let b=format!("{}",b);
                    if b.contains('+') {
                        write!(f,"({})*sqrt({})",b,r)
                    }else{
                        write!(f,"{}*sqrt({})",b,r)
                    }
                }
            }
        }
    }
}

impl Add for &Constructible {
    type Output = Constructible;
    fn add(self, other: Self) -> Constructible {
        match (self, other) {
            (Rat(rhs), Rat(lhs)) => Rat(rhs + lhs),
            (
                Con {
                    ref a,
                    ref b,
                    ref r,
                },
                Con {
                    a: ref a2,
                    b: ref b2,
                    r: ref r2,
                },
            ) if eq_rep(r, r2) => Con {
                a: Rc::new((&**a) + a2),
                b: Rc::new((&**b) + b2),
                r: Rc::clone(r),
            },
            (x, Con { a, b, r }) if x.strict_subfield(other) => Con {
                a: Rc::new((&**a) + x),
                b: Rc::clone(b),
                r: Rc::clone(r),
            },
            (Con { a, b, r }, x) if x.strict_subfield(self) => Con {
                a: Rc::new((&**a) + x),
                b: Rc::clone(b),
                r: Rc::clone(r),
            },
            _ => &self.join(other) + other,
        }
    }
}

impl Div for &Constructible {
    type Output = Constructible;
    fn div(self, other: Self) -> Constructible {
        self * &other.inverse()
    }
}

impl Mul for &Constructible {
    type Output = Constructible;
    fn mul(self, other: Self) -> Constructible {
        match (self, other) {
            (Rat(rhs), Rat(lhs)) => Rat(rhs * lhs),
            (
                Con {
                    ref a,
                    ref b,
                    ref r,
                },
                Con {
                    a: ref a2,
                    b: ref b2,
                    r: ref r2,
                },
            ) if eq_rep(r, r2) => {
                let a = &**a;
                let b = &**b;
                let a2 = &**a2;
                let b2 = &**b2;
                let a_times_a2 = a * a2;
                let b_times_b2 = b * b2;
                let a_plus_b_times_a2_plus_b2 = &(a + b) * &(a2 + b2);
                Con {
                    a: Rc::new(&a_times_a2 + &(&b_times_b2 * r)),
                    b: Rc::new(&(&a_plus_b_times_a2_plus_b2 - &a_times_a2) - &b_times_b2),
                    r: Rc::clone(r),
                }
            }
            (x, Con { a, b, r }) if x.strict_subfield(other) => Con {
                a: Rc::new((&**a) * x),
                b: Rc::new((&**b) * x),
                r: Rc::clone(r),
            },
            (Con { a, b, r }, x) if x.strict_subfield(self) => Con {
                a: Rc::new((&**a) * x),
                b: Rc::new((&**b) * x),
                r: Rc::clone(r),
            },
            _ => &self.join(other) * other,
        }
    }
}

impl Neg for &Constructible {
    type Output = Constructible;
    fn neg(self) -> Constructible {
        match self {
            Rat(x) => Rat(-x),
            Con { a, b, r } => Con {
                a: Rc::new(<&Constructible>::neg(a)),
                b: Rc::new(<&Constructible>::neg(b)),
                r: Rc::clone(r),
            },
        }
    }
}

impl Sub for &Constructible {
    type Output = Constructible;
    fn sub(self, other: Self) -> Constructible {
        self + &(-other)
    }
}

impl Eq for Constructible {}

impl Ord for Constructible {
    fn cmp(&self, other: &Self) -> Ordering {
        use core::cmp::Ordering::*;
        match self - other {
            Rat(x) => rational::Rational::cmp(&x, &rational::Rational::from_integer(0)),
            Con {
                ref a,
                ref b,
                ref r,
            } => match (
                Constructible::cmp(a, &(Constructible::from_integer(0))),
                Constructible::cmp(b, &(Constructible::from_integer(0))),
            ) {
                (Less, Less) => Less,
                (Less, Equal) => Less,
                (Less, Greater) => Constructible::cmp(&(&(&**b * b) * r), &(&**a * a)),
                (Equal, Less) => Less,
                (Equal, Equal) => Equal,
                (Equal, Greater) => Greater,
                (Greater, Less) => Constructible::cmp(&(&**a * a), &(&(&**b * b) * r)),
                (Greater, Equal) => Greater,
                (Greater, Greater) => Greater,
            },
        }
    }
}

impl PartialEq for Constructible {
    fn eq(&self, other: &Self) -> bool {
        (self - other).is_zero()
    }
}

impl PartialOrd for Constructible {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(Constructible::cmp(self, other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn division() {
        assert_eq!(
            (&Con {
                a: Rc::new(Rat(rational::Rational::from_integer(19))),
                b: Rc::new(Rat(rational::Rational::from_integer(5))),
                r: Rc::new(Rat(rational::Rational::from_integer(3)))
            } / &Con {
                a: Rc::new(Rat(rational::Rational::from_integer(1))),
                b: Rc::new(Rat(rational::Rational::from_integer(2))),
                r: Rc::new(Rat(rational::Rational::from_integer(3)))
            }),
            Con {
                a: Rc::new(Rat(rational::Rational::from_integer(1))),
                b: Rc::new(Rat(rational::Rational::from_integer(3))),
                r: Rc::new(Rat(rational::Rational::from_integer(3)))
            }
        )
    }

    #[test]
    fn equivalence() {
        assert!(Constructible::from_integer(2) == Constructible::from_integer(2));
    }

    #[test]
    fn multiplication() {
        assert_eq!(
            Constructible::from_integer(6).sqrt(),
            &Constructible::from_integer(3).sqrt() * &Constructible::from_integer(2).sqrt(),
        );
        assert_eq!(
            Constructible::from_integer(2).sqrt(),
            &((&Constructible::from_integer(3).sqrt()+&Constructible::from_integer(1)).sqrt())
            * &((&Constructible::from_integer(3).sqrt()-&Constructible::from_integer(1)).sqrt()),
        );
    }

    #[test]
    fn printing(){
        let a=(&Constructible::from_integer(3).sqrt()+&Constructible::from_integer(1)).sqrt();
        print!("{}={}",a,a.to_float());
    }

    #[test]
    fn distributivity() {
        let a = Constructible::from_integer(5).sqrt().sqrt().sqrt();
        let b = Constructible::from_integer(5).sqrt().sqrt();
        let c = &a + &b;
        assert_eq!(
            &(&a + &b) * &(&a + &c),
            &(&(&b + &(&a * &c)) + &(&a * &b)) + &(&b * &c),
        );
    }

    #[test]
    fn comparison() {
        let a = Constructible::from_integer(5).sqrt().sqrt();
        let b = Constructible::from_integer(5).sqrt();
        let c = &a + &b;
        assert_eq!(a, b.sqrt());
        assert!(b > a && c > b && c > a);
    }

    #[test]
    fn sqrt() {
        let a = Constructible::from_integer(4);
        let b = Constructible::from_integer(2);
        assert_eq!(a.sqrt(), b);
        assert_eq!(
            Con {
                a: Rc::new(Rat(rational::Rational::from_integer(3))),
                b: Rc::new(Rat(rational::Rational::from_integer(2))),
                r: Rc::new(Rat(rational::Rational::from_integer(2)))
            }
            .sqrt(),
            Con {
                a: Rc::new(Rat(rational::Rational::from_integer(1))),
                b: Rc::new(Rat(rational::Rational::from_integer(1))),
                r: Rc::new(Rat(rational::Rational::from_integer(2)))
            }
        );
    }
}
