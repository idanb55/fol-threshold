using System;
using System.Collections.Generic;
using System.Linq;
using FolThresholdParser.BapaFormula;
using FolThresholdParser.Parser;
using FolThresholdParser.Utils;

namespace FolThresholdParser.FolThresholdEntities
{
    public abstract class NaturalExpression : IExpression
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
                    leftExpr = new NatConstMulExpression((NatConstExpression) leftExpr,
                        Parse(tokens.Skip(2).Take(innerLength)));
                    cursor += innerLength + 1;
                }
                else if (tokens[1].Type == SyntaxKind.VariableNameToken)
                {
                    leftExpr = new NatConstMulExpression((NatConstExpression) leftExpr,
                        new NatVarExpression(tokens[1].Value));
                    ++cursor;
                }
            }

            return cursor >= tokens.Length
                ? leftExpr
                : new NatOpExpression(leftExpr, tokens[cursor].Type, Parse(tokens.Skip(cursor + 1)));
        }

        public abstract BapaNatExpression ToBapaNatExpression();
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

        public override BapaNatExpression ToBapaNatExpression()
        {
            return new BapaNatConst(Constant);
        }

        public override string ToString()
        {
            return Constant.ToString();
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

        public override BapaNatExpression ToBapaNatExpression()
        {
            return new BapaNatVar(Name);
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

        public NatConstMulExpression(NatConstExpression constant, NaturalExpression expr)
        {
            Constant = constant;
            Expr = expr;
        }

        public override IEnumerable<string> VariablesToBind => Expr.VariablesToBind;

        public override BapaNatExpression ToBapaNatExpression()
        {
            return new BapaNatConstantMul(Constant.Constant, Expr.ToBapaNatExpression());
        }

        public override string ToString()
        {
            return Expr is NatVarExpression ? $"{Constant}{Expr}" : $"{Constant}({Expr})";
        }
    }

    public class NatOpExpression : NaturalExpression
    {
        public NaturalExpression Expr1 { get; protected set; }
        public SyntaxKind Op { get; protected set; }
        public NaturalExpression Expr2 { get; protected set; }

        public override IEnumerable<string> VariablesToBind => Expr1.VariablesToBind.Concat(Expr2.VariablesToBind);

        public NatOpExpression(NaturalExpression expr1, SyntaxKind natOperation, NaturalExpression expr2)
        {
            Expr1 = expr1;
            Op = natOperation;
            Expr2 = expr2;
        }

        private static BapaNatOperation.NatRelation GetOperation(SyntaxKind op)
        {
            switch (op)
            {
                case SyntaxKind.PlusOperationToken:
                    return BapaNatOperation.NatRelation.Plus;
                case SyntaxKind.MinusOperationToken:
                    return BapaNatOperation.NatRelation.Minus;
                default:
                    throw new Exception("Illegal Natural operation");
            }
        }

        public override BapaNatExpression ToBapaNatExpression()
        {
            return new BapaNatOperation(GetOperation(Op), Expr1.ToBapaNatExpression(), Expr2.ToBapaNatExpression());
        }

        public override string ToString()
        {
            return $"{Expr1} {Tokenizer.Keywords[Op]} {Expr2}";
        }
    }
}
