using System;
using System.Collections.Generic;
using System.Linq;
using FolThresholdParser.Parser;
using FolThresholdParser.Utils;

namespace FolThresholdParser.FolSyntax
{
    public abstract class NaturalExpression
    {
        public abstract IEnumerable<string> VariablesToBind { get; }

        public static NaturalExpression Parse(ArrayView<Token> tokens)
        {
            var cursor = 0;
            NaturalExpression leftExpr = null;
            if (tokens[0].Type == SyntaxKind.OpenParenthesisToken)
            {
                var innerLength = tokens.Skip(cursor).IndexOfCloseParenthesis();
                leftExpr = Parse(tokens.Skip(1).Take(innerLength));
                cursor += innerLength + 1;
            }
            else if (tokens[0].Type == SyntaxKind.VariableNameToken)
            {
                leftExpr = new NatVarExpression(tokens[0].Value);
                ++cursor;
            }
            else if (tokens[0].Type == SyntaxKind.LiteralNumberToken)
            {
                leftExpr = new NatConstExpression(int.Parse(tokens[0].Value));
                ++cursor;
                if (tokens[1].Type == SyntaxKind.OpenParenthesisToken)
                {
                    var innerLength = tokens.Skip(cursor).IndexOfCloseParenthesis();
                    leftExpr = NatConstMulExpression.Mul((NatConstExpression) leftExpr,
                        Parse(tokens.Skip(2).Take(innerLength)));
                    cursor += innerLength + 1;
                }
                else if (tokens[1].Type == SyntaxKind.VariableNameToken)
                {
                    leftExpr = NatConstMulExpression.Mul((NatConstExpression) leftExpr,
                        new NatVarExpression(tokens[1].Value));
                    ++cursor;
                }
            }

            if (cursor + 2 < tokens.Length && tokens[cursor+1].Type == SyntaxKind.DivOperationToken && tokens[cursor+2].Type == SyntaxKind.LiteralNumberToken)
            {
                return new NatConstDivExpression(int.Parse(tokens[cursor + 2].Value), leftExpr);
            }

            return cursor >= tokens.Length
                ? leftExpr
                : new NatOpExpression(leftExpr, tokens[cursor].Type, Parse(tokens.Skip(cursor + 1)));
        }

        public abstract string GetSmtAssert(Dictionary<string, Identifier> identifiers);
    }

    public class NatConstExpression : NaturalExpression
    {
        public int Constant { get; protected set; }

        public NatConstExpression(int constant)
        {
            Constant = constant;
        }

        public override IEnumerable<string> VariablesToBind
        {
            get
            {
                yield break;
            }
        }

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers)
        {
            return ToString();
        }

        public override string ToString()
        {
            return Constant.ToString();
        }

        public static implicit operator int(NatConstExpression constant)
        {
            return constant.Constant;
        }

        public static implicit operator NatConstExpression(int constant)
        {
            return new NatConstExpression(constant);
        }

    }

    public class NatVarExpression : NaturalExpression
    {
        public string Name { get; protected set; }

        public NatVarExpression(string name)
        {
            Name = name;
        }

        public override IEnumerable<string> VariablesToBind
        {
            get
            {
                yield break;
            }
        }

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers)
        {
            return ToString();
        }

        public override string ToString()
        {
            return Name;
        }
    }

    public class NatConstMulExpression : NaturalExpression
    {
        public NatConstExpression Constant { get; protected set; }
        public NaturalExpression Expr { get; protected set; }

        private NatConstMulExpression(NatConstExpression constant, NaturalExpression expr)
        {
            Constant = constant;
            Expr = expr;
        }

        public static NaturalExpression Mul(int constant, NaturalExpression expr)
        {
            if (constant == 1) return expr;
            return new NatConstMulExpression(constant, expr);
        }

        public override IEnumerable<string> VariablesToBind => Expr.VariablesToBind;
        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers)
        {
            return $"(* {Constant.GetSmtAssert(identifiers)} {Expr.GetSmtAssert(identifiers)})";
        }

        public override string ToString()
        {
            return Expr is NatVarExpression ? $"{Constant}{Expr}" : $"{Constant}({Expr})";
        }
    }

    public class NatConstDivExpression : NaturalExpression
    {
        public NatConstExpression Constant { get; protected set; }
        public NaturalExpression Expr { get; protected set; }

        public NatConstDivExpression(NatConstExpression constant, NaturalExpression expr)
        {
            Constant = constant;
            Expr = expr;
        }

        public static int Gcd(int a, int b)
        {
            return b == 0 ? a : Gcd(b, a % b);
        }

        public static Tuple<NaturalExpression, int> Reduce(NaturalExpression expression)
        {
            var div = expression as NatConstDivExpression;
            if (div != null)
            {
                var inner = Reduce(div.Expr);
                return new Tuple<NaturalExpression, int>(inner.Item1, inner.Item2 * div.Constant);
            }

            if (expression is NatConstExpression)
            {
                return new Tuple<NaturalExpression, int>(expression, 1);
            }

            var mul = expression as NatConstMulExpression;
            if (mul != null)
            {
                var inner = Reduce(mul.Expr);
                int gcd = Gcd(mul.Constant, inner.Item2);
                return new Tuple<NaturalExpression, int>(NatConstMulExpression.Mul(mul.Constant / gcd, inner.Item1), inner.Item2 / gcd);
            }

            if (expression is NatVarExpression)
            {
                return new Tuple<NaturalExpression, int>(expression, 1);
            }

            if (expression is NatCardExpression)
            {
                return new Tuple<NaturalExpression, int>(expression, 1);
            }

            var op = expression as NatOpExpression;
            if (op != null)
            {
                var inner1 = Reduce(op.Expr1);
                var inner2 = Reduce(op.Expr2);
                int gcd = Gcd(inner1.Item2, inner2.Item2);
                return new Tuple<NaturalExpression, int>(new NatOpExpression(
                        NatConstMulExpression.Mul(inner2.Item2 / gcd, inner1.Item1),
                        op.Op,
                        NatConstMulExpression.Mul(inner1.Item2 / gcd, inner2.Item1)
                    ), (inner1.Item2 * inner2.Item2) / gcd);
            }

            throw new Exception($"Unhandled type of expression in Reduce function: {expression.GetType()}");
        }

        public override IEnumerable<string> VariablesToBind => Expr.VariablesToBind;
        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers)
        {
            throw new NotImplementedException();
        }

        public override string ToString()
        {
            return Expr is NatVarExpression ? $"{Expr} / {Constant}" : $"({Expr}) / {Constant}";
        }
    }

    public class NatCardExpression : NaturalExpression
    {
        public SetExpression SetExpr { get; protected set; }

        public NatCardExpression(SetExpression setExpr)
        {
            SetExpr = setExpr;
        }

        public override IEnumerable<string> VariablesToBind => SetExpr.VariablesToBind;

        public override string ToString()
        {
            return $"|{SetExpr}|";
        }

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers)
        {
            return $"(card {SetExpr.GetSmtAssert(identifiers)})";
        }
    }

    public class NatOpExpression : NaturalExpression
    {
        public NaturalExpression Expr1 { get; protected set; }
        public NatRelation Op { get; protected set; }
        public NaturalExpression Expr2 { get; protected set; }

        public override IEnumerable<string> VariablesToBind => Expr1.VariablesToBind.Concat(Expr2.VariablesToBind);
        
        public NatOpExpression(NaturalExpression expr1, NatRelation natOperation, NaturalExpression expr2)
        {
            Expr1 = expr1;
            Op = natOperation;
            Expr2 = expr2;
        }

        public NatOpExpression(NaturalExpression expr1, SyntaxKind natOperation, NaturalExpression expr2) : this(expr1, (NatRelation)natOperation, expr2)
        {
        }

        public static NaturalExpression Aggregate(SyntaxKind setOperation, NaturalExpression[] expressions)
        {
            return expressions.Aggregate((expr1, expr2) => new NatOpExpression(expr1, setOperation, expr2));
        }

        public enum NatRelation
        {
            Plus = SyntaxKind.PlusOperationToken, Minus = SyntaxKind.MinusOperationToken
        }

        public override string ToString()
        {
            return $"{Expr1} {Tokenizer.Keywords[(SyntaxKind)Op]} {Expr2}";
        }

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers)
        {
            return
                $"({Tokenizer.Keywords[(SyntaxKind) Op]} {Expr1.GetSmtAssert(identifiers)} {Expr2.GetSmtAssert(identifiers)})";
        }
    }
}
