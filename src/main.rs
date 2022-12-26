use chumsky::{
    prelude::{recursive, skip_then_retry_until, Parser, Simple},
    primitive::{just, one_of, take_until},
    select,
    stream::Stream,
    text::{self, TextParser},
};
use once_cell::sync::Lazy;
use std::{env, fs};

type EffectP = u8;

#[derive(Debug, Clone, PartialEq)]
struct Var {
    term: String,
}

impl Var {
    pub fn new(term: String) -> Var {
        Var { term }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Fun {
    first: String,
    second: Term,
}

impl Fun {
    pub fn new<'a>(first: String, second: Term) -> Fun {
        Fun { first, second }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Eff {
    term: EffectP,
}

impl Eff {
    pub fn new(term: EffectP) -> Eff {
        Eff { term }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct AtOp {
    first: Term,
    second: Term,
}

impl AtOp {
    pub fn new(first: Term, second: Term) -> AtOp {
        AtOp { first, second }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Perform {
    first: Term,
    second: Term,
}

impl Perform {
    pub fn new(first: Term, second: Term) -> Perform {
        Perform { first, second }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Let {
    first: String,
    second: Term,
    third: Term,
}

impl Let {
    pub fn new(first: String, second: Term, third: Term) -> Let {
        Let {
            first,
            second,
            third,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct WithH {
    first: Term,
    second: Term,
}

impl WithH {
    pub fn new(first: Term, second: Term) -> WithH {
        WithH { first, second }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Handler {
    first: Term,
    second: (String, Term),
    third: (String, String, Term),
}

impl Handler {
    pub fn new(first: Term, second: (String, Term), third: (String, String, Term)) -> Handler {
        Handler {
            first,
            second,
            third,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Int {
    term: u8,
}

impl Int {
    pub fn new(term: u8) -> Int {
        Int { term }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct PlusOp {
    first: Term,
    second: Term,
}

impl PlusOp {
    fn new(first: Term, second: Term) -> PlusOp {
        PlusOp { first, second }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct MinusOp {
    first: Term,
    second: Term,
}

impl MinusOp {
    fn new(first: Term, second: Term) -> MinusOp {
        MinusOp { first, second }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct MulOp {
    first: Term,
    second: Term,
}

impl MulOp {
    fn new(first: Term, second: Term) -> MulOp {
        MulOp { first, second }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct DivOp {
    first: Term,
    second: Term,
}

impl DivOp {
    fn new(first: Term, second: Term) -> DivOp {
        DivOp { first, second }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Term {
    Var(Var),
    Fun(Box<Fun>),
    Eff(Eff),
    AtOp(Box<AtOp>),
    Perform(Box<Perform>),
    Let(Box<Let>),
    Inst,
    WithH(Box<WithH>),
    Handler(Box<Handler>),
    Int(Int),
    PlusOp(Box<PlusOp>),
    MinusOp(Box<MinusOp>),
    MulOp(Box<MulOp>),
    DivOp(Box<DivOp>),
    Abort,
}

type Stack = Vec<Box<dyn Fn(Term) -> Term>>;

fn flatfn(stack: Stack) -> impl Fn(Term) -> Term {
    move |x| {
        let mut ret = x;
        for f in &stack {
            ret = f(ret);
        }
        ret
    }
}

// Termが値か式か判定
fn valuable(term: &Term) -> bool {
    match term {
        &Term::Var(_) => true,
        &Term::Handler(_) => true,
        &Term::Fun(_) => true,
        &Term::Eff(_) => true,
        &Term::Int(_) => true,
        &Term::Abort => true,
        _ => false,
    }
}

fn substitutes(term: Term, y: String, t: Term) -> Term {
    match term {
        Term::Var(x) => {
            if x.term == y {
                t
            } else {
                Term::Var(x)
            }
        }
        Term::Fun(x) => {
            if x.first == y {
                Term::Fun(x)
            } else {
                Term::Fun(Box::new(Fun::new(x.first, substitutes(x.second, y, t))))
            }
        }
        Term::AtOp(x) => Term::AtOp(Box::new(AtOp::new(
            substitutes(x.first, y.clone(), t.clone()),
            substitutes(x.second, y, t),
        ))),
        Term::Perform(x) => Term::Perform(Box::new(Perform::new(
            substitutes(x.first, y.clone(), t.clone()),
            substitutes(x.second, y, t),
        ))),
        Term::Let(x) => {
            if x.first == y {
                Term::Let(Box::new(Let::new(
                    x.first,
                    substitutes(x.second, y, t),
                    x.third,
                )))
            } else {
                Term::Let(Box::new(Let::new(
                    x.first,
                    substitutes(x.second, y.clone(), t.clone()),
                    substitutes(x.third, y, t),
                )))
            }
        }
        Term::WithH(x) => Term::WithH(Box::new(WithH::new(
            substitutes(x.first, y.clone(), t.clone()),
            substitutes(x.second, y, t),
        ))),
        Term::Handler(x) => Term::Handler(Box::new(Handler::new(
            substitutes(x.first, y.clone(), t.clone()),
            if x.second.0 == y {
                x.second
            } else {
                (x.second.0, substitutes(x.second.1, y.clone(), t.clone()))
            },
            if x.third.0 == y || x.third.1 == y {
                x.third
            } else {
                (x.third.0, x.third.1, substitutes(x.third.2, y, t))
            },
        ))),
        Term::PlusOp(x) => Term::PlusOp(Box::new(PlusOp::new(
            substitutes(x.first, y.clone(), t.clone()),
            substitutes(x.second, y, t),
        ))),
        Term::MinusOp(x) => Term::MinusOp(Box::new(MinusOp::new(
            substitutes(x.first, y.clone(), t.clone()),
            substitutes(x.second, y, t),
        ))),
        Term::MulOp(x) => Term::MulOp(Box::new(MulOp::new(
            substitutes(x.first, y.clone(), t.clone()),
            substitutes(x.second, y, t),
        ))),
        Term::DivOp(x) => Term::DivOp(Box::new(DivOp::new(
            substitutes(x.first, y.clone(), t.clone()),
            substitutes(x.second, y, t),
        ))),
        _ => term,
    }
}

fn substitutes_for_list(t: Term, list: Vec<(String, Term)>) -> Term {
    let mut acc = t;
    for (x, u) in list.into_iter() {
        acc = substitutes(acc, x, u);
    }
    acc
}

// 四則演算の計算
fn binapp(term: Term) -> Term {
    match term {
        Term::PlusOp(x) => match *x {
            PlusOp {
                first: Term::Int(Int { term: lhs }),
                second: Term::Int(Int { term: rhs }),
            } => Term::Int(Int::new(lhs + rhs)),
            _ => panic!("PlusOp Error"),
        },
        Term::MinusOp(x) => match *x {
            MinusOp {
                first: Term::Int(Int { term: lhs }),
                second: Term::Int(Int { term: rhs }),
            } => Term::Int(Int::new(lhs - rhs)),
            _ => panic!("MinusOp Error"),
        },
        Term::MulOp(x) => match *x {
            MulOp {
                first: Term::Int(Int { term: lhs }),
                second: Term::Int(Int { term: rhs }),
            } => Term::Int(Int::new(lhs * rhs)),
            _ => panic!("MulOp Error"),
        },
        Term::DivOp(x) => match *x {
            DivOp {
                first: Term::Int(Int { term: lhs }),
                second: Term::Int(Int { term: rhs }),
            } => Term::Int(Int::new(lhs / rhs)),
            _ => panic!("DivOp Error"),
        },
        _ => panic!("Binapp Error"),
    }
}

type Model = (Term, Stack, Stack);

static HOLE: Lazy<Term> = Lazy::new(|| {
    Term::Var(Var {
        term: "□".to_string(),
    })
});

type World = (EffectP, Model);

fn kfunc(stack: Stack) -> Term {
    let var = "◇".to_string();
    Term::Fun(Box::new(Fun::new(
        var.clone(),
        flatfn(stack)(Term::Var(Var::new(var))),
    )))
}

fn vh(hander: Term) -> (String, Term) {
    match hander {
        Term::Handler(x) => x.second,
        _ => panic!("Handler only!"),
    }
}

fn handle_or_throw(
    eff: Term,
    e: Term,
    v: Term,
    mut s: Stack,
    mut es: Stack,
) -> (Term, Stack, Stack) {
    let f = s.pop();
    match f {
        None => (Term::Abort, s, es),
        Some(f) => match f(HOLE.clone()) {
            Term::WithH(x) => match *x {
                WithH { first, second } if second == Lazy::get(&HOLE).unwrap().clone() => {
                    match first {
                        Term::Handler(x) => match *x {
                            Handler {
                                first: eff2,
                                second: _,
                                third: (x, k, e),
                            } if eff2 == eff => {
                                let k2 = kfunc(es);
                                let vec = vec![(x, v), (k, k2)];
                                let e2 = substitutes_for_list(e, vec);
                                s.push(f);
                                (e2, s, Vec::new())
                            }
                            _ => {
                                es.push(f);
                                (Term::Perform(Box::new(Perform::new(eff, e))), s, es)
                            }
                        },
                        _ => {
                            es.push(f);
                            (Term::Perform(Box::new(Perform::new(eff, e))), s, es)
                        }
                    }
                }
                _ => {
                    es.push(f);
                    (Term::Perform(Box::new(Perform::new(eff, e))), s, es)
                }
            },
            _ => {
                es.push(f);
                (Term::Perform(Box::new(Perform::new(eff, e))), s, es)
            }
        },
    }
}

fn eval1(world: World) -> World {
    let (effectp, model) = world;
    match model {
        (Term::Inst, s, es) => (effectp + 1, (Term::Eff(Eff::new(effectp + 1)), s, es)),
        (Term::Fun(x), s, es) => match *x {
            Fun {
                first: x,
                second: Term::AtOp(y),
            } if valuable(&y.second) => (effectp, (substitutes(y.first, x, y.second), s, es)),
            _ => panic!(""),
        },
        (Term::AtOp(x), mut s, es) => match *x {
            AtOp {
                first: f,
                second: e,
            } => match f {
                Term::Fun(func) if valuable(&e) => {
                    (effectp, (substitutes(func.second, func.first, e), s, es))
                }
                _ if valuable(&f) => {
                    let closure =
                        move |term: Term| Term::AtOp(Box::new(AtOp::new(f.clone(), term)));
                    s.push(Box::new(closure));
                    (effectp, (e, s, es))
                }
                _ => {
                    let closure =
                        move |term: Term| Term::AtOp(Box::new(AtOp::new(term, e.clone())));
                    s.push(Box::new(closure));
                    (effectp, (f, s, es))
                }
            },
        },
        (Term::PlusOp(x), mut s, es) => match *x {
            PlusOp {
                first: e1,
                second: e2,
            } if valuable(&e1) && valuable(&e2) => (
                effectp,
                (binapp(Term::PlusOp(Box::new(PlusOp::new(e1, e2)))), s, es),
            ),
            PlusOp {
                first: e1,
                second: e2,
            } if valuable(&e1) => {
                let closure =
                    move |term: Term| Term::PlusOp(Box::new(PlusOp::new(e1.clone(), term)));
                s.push(Box::new(closure));
                (effectp, (e2, s, es))
            }
            PlusOp {
                first: e1,
                second: e2,
            } => {
                let closure =
                    move |term: Term| Term::PlusOp(Box::new(PlusOp::new(term, e2.clone())));
                s.push(Box::new(closure));
                (effectp, (e1, s, es))
            }
        },
        (Term::MinusOp(x), mut s, es) => match *x {
            MinusOp {
                first: e1,
                second: e2,
            } if valuable(&e1) && valuable(&e2) => (
                effectp,
                (binapp(Term::MinusOp(Box::new(MinusOp::new(e1, e2)))), s, es),
            ),
            MinusOp {
                first: e1,
                second: e2,
            } if valuable(&e1) => {
                let closure =
                    move |term: Term| Term::MinusOp(Box::new(MinusOp::new(e1.clone(), term)));
                s.push(Box::new(closure));
                (effectp, (e2, s, es))
            }
            MinusOp {
                first: e1,
                second: e2,
            } => {
                let closure =
                    move |term: Term| Term::MinusOp(Box::new(MinusOp::new(term, e2.clone())));
                s.push(Box::new(closure));
                (effectp, (e1, s, es))
            }
        },
        (Term::MulOp(x), mut s, es) => match *x {
            MulOp {
                first: e1,
                second: e2,
            } if valuable(&e1) && valuable(&e2) => (
                effectp,
                (binapp(Term::MulOp(Box::new(MulOp::new(e1, e2)))), s, es),
            ),
            MulOp {
                first: e1,
                second: e2,
            } if valuable(&e1) => {
                let closure = move |term: Term| Term::MulOp(Box::new(MulOp::new(e1.clone(), term)));
                s.push(Box::new(closure));
                (effectp, (e2, s, es))
            }
            MulOp {
                first: e1,
                second: e2,
            } => {
                let closure = move |term: Term| Term::MulOp(Box::new(MulOp::new(term, e2.clone())));
                s.push(Box::new(closure));
                (effectp, (e1, s, es))
            }
        },
        (Term::DivOp(x), mut s, es) => match *x {
            DivOp {
                first: e1,
                second: e2,
            } if valuable(&e1) && valuable(&e2) => (
                effectp,
                (binapp(Term::DivOp(Box::new(DivOp::new(e1, e2)))), s, es),
            ),
            DivOp {
                first: e1,
                second: e2,
            } if valuable(&e1) => {
                let closure = move |term: Term| Term::DivOp(Box::new(DivOp::new(e1.clone(), term)));
                s.push(Box::new(closure));
                (effectp, (e2, s, es))
            }
            DivOp {
                first: e1,
                second: e2,
            } => {
                let closure = move |term: Term| Term::DivOp(Box::new(DivOp::new(term, e2.clone())));
                s.push(Box::new(closure));
                (effectp, (e1, s, es))
            }
        },
        (Term::Let(x), mut s, es) => match *x {
            Let {
                first: x,
                second: e,
                third: body,
            } if valuable(&e) => (effectp, (substitutes(body, x, e), s, es)),
            Let {
                first: x,
                second: e,
                third: body,
            } => {
                let closure =
                    move |term: Term| Term::Let(Box::new(Let::new(x.clone(), term, body.clone())));
                s.push(Box::new(closure));
                (effectp, (e, s, es))
            }
        },
        (Term::WithH(x), mut s, es) => match *x {
            WithH {
                first: h,
                second: e,
            } if valuable(&e) => {
                let (x, ev) = vh(h);
                (effectp, (substitutes(ev, x, e), s, es))
            }
            WithH {
                first: h,
                second: e,
            } => {
                let closure = move |term: Term| Term::WithH(Box::new(WithH::new(h.clone(), term)));
                s.push(Box::new(closure));
                (effectp, (e, s, es))
            }
        },
        (Term::Perform(x), mut s, es) => match *x {
            Perform {
                first: eff,
                second: e,
            } if valuable(&eff) && valuable(&e) => {
                (effectp, handle_or_throw(eff, e.clone(), e, s, es))
            }
            Perform {
                first: eff,
                second: e,
            } if valuable(&eff) => {
                let closure =
                    move |term: Term| Term::Perform(Box::new(Perform::new(eff.clone(), term)));
                s.push(Box::new(closure));
                (effectp, (e, s, es))
            }
            Perform {
                first: eff,
                second: e,
            } => {
                let closure =
                    move |term: Term| Term::Perform(Box::new(Perform::new(term, e.clone())));
                s.push(Box::new(closure));
                (effectp, (eff, s, es))
            }
        },
        (v, mut s, es) => {
            let f = s.pop();
            match f {
                None if valuable(&v) => (effectp, (v, s, es)),
                Some(f) if valuable(&v) => (effectp, (f(v), s, es)),
                _ => panic!(""),
            }
        }
    }
}

fn go(m: (Term, Stack, Stack), idx: EffectP) -> Term {
    match eval1((idx, m)) {
        (_, (v, s, _)) if s.is_empty() && valuable(&v) => v,
        (idx, m_) => go(m_, idx),
    }
}

fn eval(t: Term, s: Stack, es: Stack, idx: EffectP) -> Term {
    go((t, s, es), idx)
}

fn run(t: Term) -> Term {
    eval(t, Vec::new(), Vec::new(), 0)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Token {
    Ctrl(char),
    Int(String),
    Op(String),
    Ident(String),
    Let,
    In,
    Val,
    Perform,
    Inst,
    With,
    Handle,
    Handler,
    Fun,
    Arrow,
}

type Span = std::ops::Range<usize>;
fn lexer() -> impl Parser<char, Vec<(Token, Span)>, Error = Simple<char>> {
    let ctrl = one_of("()[]{};,").map(|c| Token::Ctrl(c));
    let int = text::int(10)
        .chain::<char, _, _>(just('.').chain(text::digits(10)).or_not().flatten())
        .collect::<String>()
        .map(Token::Int);
    let op = one_of("+-*/=")
        .repeated()
        .at_least(1)
        .collect::<String>()
        .map(Token::Op);
    let ident = text::ident().map(|ident: String| match ident.as_str() {
        "let" => Token::Let,
        "in" => Token::In,
        "val" => Token::Val,
        "perform" => Token::Perform,
        "inst" => Token::Inst,
        "with" => Token::With,
        "handle" => Token::Handle,
        "handler" => Token::Handler,
        "fun" => Token::Fun,
        _ => Token::Ident(ident),
    });
    let arrow = just("->").map(|_| Token::Arrow);
    let token = int
        .or(arrow)
        .or(op)
        .or(ctrl)
        .or(ident)
        .recover_with(skip_then_retry_until([]));
    let comment = just("//").then(take_until(just('\n'))).padded();

    token
        .map_with_span(|tok, span| (tok, span))
        .padded_by(comment.repeated())
        .padded()
        .repeated()
}

fn expr_parser() -> impl Parser<Token, Term, Error = Simple<Token>> + Clone {
    recursive(|term| {
        let raw_term = recursive(|raw_term| {
            let int = select! {
                Token::Int(n) => Term::Int(Int::new(n.parse().unwrap())),
            }
            .labelled("int");
            let ident = select! { Token::Ident(ident) => ident.clone() }.labelled("identifier");
            let let_in = just(Token::Let)
                .ignore_then(ident)
                .then_ignore(just(Token::Op("=".to_string())))
                .then(raw_term.clone())
                .then_ignore(just(Token::In))
                .then(term)
                .map(|((first, second), third)| {
                    Term::Let(Box::new(Let::new(first, second, third)))
                });
            let handler = just(Token::Handler)
                .ignore_then(ident)
                .then_ignore(just(Token::Ctrl('(')))
                .then_ignore(just(Token::Val))
                .then(ident)
                .then_ignore(just(Token::Arrow))
                .then(raw_term.clone())
                .then_ignore(just(Token::Ctrl(')')))
                .then_ignore(just(Token::Ctrl('(')))
                .then_ignore(just(Token::Ctrl('(')))
                .then(ident)
                .then_ignore(just(Token::Ctrl(',')))
                .then(ident)
                .then_ignore(just(Token::Ctrl(')')))
                .then_ignore(just(Token::Arrow))
                .then(raw_term.clone())
                .then_ignore(just(Token::Ctrl(')')))
                .map(|(((((a, b), c), d), e), f)| {
                    Term::Handler(Box::new(Handler::new(
                        Term::Var(Var::new(a)),
                        (b, c),
                        (d, e, f),
                    )))
                });
            let vexpr0 = just(Token::Ctrl('('))
                .ignore_then(raw_term.clone())
                .then_ignore(just(Token::Ctrl(')')))
                .or(ident.map(|s| Term::Var(Var::new(s))));
            let with_h = just(Token::With)
                .ignore_then(vexpr0.clone())
                .then_ignore(just(Token::Handle))
                .then(raw_term.clone())
                .map(|(a, b)| Term::WithH(Box::new(WithH::new(a, b))));
            let inst = just(Token::Inst)
                .ignore_then(just(Token::Ctrl('(')))
                .ignore_then(just(Token::Ctrl(')')))
                .map(|_| Term::Inst);
            let perform = just(Token::Perform)
                .ignore_then(ident)
                .then(raw_term.clone())
                .map(|(a, b)| Term::Perform(Box::new(Perform::new(Term::Var(Var::new(a)), b))));
            let expr0 = vexpr0.clone().or(int);
            let app = vexpr0
                .clone()
                .then(expr0.clone().repeated())
                .foldl(|a, b| Term::AtOp(Box::new(AtOp::new(a, b))));
            let expr1 = inst.or(perform).or(app).or(expr0);
            let atom = int.or(let_in).or(handler).or(with_h);
            let op = just(Token::Op("*".to_string()));
            let multiple = atom
                .or(expr1.clone())
                .then(op.then(expr1).repeated())
                .foldl(|a, (_, b)| Term::MulOp(Box::new(MulOp::new(a, b))));
            let op = just(Token::Op("/".to_string()));
            let div = multiple
                .clone()
                .then(op.then(multiple).repeated())
                .foldl(|a, (_, b)| Term::DivOp(Box::new(DivOp::new(a, b))));
            let op = just(Token::Op("+".to_string()));
            let plus = div
                .clone()
                .then(op.then(div).repeated())
                .foldl(|a, (_, b)| Term::PlusOp(Box::new(PlusOp::new(a, b))));
            let op = just(Token::Op("-".to_string()));
            let minus = plus
                .clone()
                .then(op.then(plus).repeated())
                .foldl(|a, (_, b)| Term::MinusOp(Box::new(MinusOp::new(a, b))));
            minus
        });
        raw_term
    })
}

fn main() {
    let src = fs::read_to_string(env::args().nth(1).expect("Expected file argument"))
        .expect("Failed to read file");
    let (tokens, errs) = lexer().parse_recovery(src.as_str());

    let _parse_errs = if let Some(tokens) = tokens {
        //dbg!(tokens);
        let len = src.chars().count();
        let (ast, parse_errs) =
            expr_parser().parse_recovery(Stream::from_iter(len..len + 1, tokens.into_iter()));
        if let Some(funcs) = ast.filter(|_| errs.len() + parse_errs.len() == 0) {
            println!("{:?}", run(funcs));
        } else {
            println!("{:?}", errs);
            println!("{:?}", parse_errs);
            panic!("Error");
        };
        parse_errs
    } else {
        Vec::new()
    };
}
