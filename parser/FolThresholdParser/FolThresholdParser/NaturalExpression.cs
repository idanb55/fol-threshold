﻿using System;
using System.Collections.Generic;
using System.Linq;

namespace FolThresholdParser
{
    public abstract class NaturalExpression : IExpression
    {
        public abstract IEnumerable<string> Variables { get; }

        private static NaturalExpression ParseSingleToken(Token token)
        {
            switch (token.Type)
            {
                case SyntaxKind.VariableNameToken:
                    return new NatVarExpression(token.Value);
                case SyntaxKind.LiteralNumberToken:
                    return new NatConstExpression(int.Parse(token.Value));
                default:
                    throw new Exception("Could not parse token");
            }
        }

        internal static NaturalExpression Parse(ArrayView<Token> tokens)
        {
            var cursor = 0;
            NaturalExpression leftExpr = null;
            if (tokens[0].Type == SyntaxKind.OpenParenthesisToken)
            {
                var innerLength = tokens.IndexOfCloseParenthesis(cursor);
                leftExpr = Parse(tokens.Skip(1).Take(innerLength).ToArray());
                cursor += innerLength + 1;
            } else if (tokens[0].Type == SyntaxKind.VariableNameToken)
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
                    var innerLength = tokens.IndexOfCloseParenthesis(cursor);
                    leftExpr = new NatConstMulExpression((NatConstExpression)leftExpr, Parse(tokens.Skip(2).Take(innerLength).ToArray()));
                    cursor += innerLength + 1;
                }
                else if (tokens[1].Type == SyntaxKind.VariableNameToken)
                {
                    leftExpr = new NatConstMulExpression((NatConstExpression)leftExpr, new NatVarExpression(tokens[1].Value));
                    ++cursor;
                }
            }
            if (cursor >= tokens.Length) return leftExpr;

            return new NatOpExpression(leftExpr, tokens[cursor].Type, Parse(tokens.Skip(cursor+1).ToArray()));
        }
    }

    public class NatConstExpression : NaturalExpression
    {
        public int Constant { get; protected set; }

        public NatConstExpression(int constant)
        {
            Constant = constant;
        }

        public override IEnumerable<string> Variables
        {
            get
            {
                yield break;
            }
        }
    }

    public class NatVarExpression : NaturalExpression
    {
        public string Name { get; protected set; }

        public NatVarExpression(string name)
        {
            Name = name;
        }

        public override IEnumerable<string> Variables
        {
            get
            {
                yield return Name;
            }
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

        public override IEnumerable<string> Variables => Expr.Variables;
    }

    public class NatOpExpression : NaturalExpression
    {
        public NaturalExpression Expr1 { get; protected set; }
        public SyntaxKind Op { get; protected set; }
        public NaturalExpression Expr2 { get; protected set; }

        public override IEnumerable<string> Variables => Expr1.Variables.Concat(Expr2.Variables);

        public NatOpExpression(NaturalExpression expr1, SyntaxKind natOperation, NaturalExpression expr2)
        {
            Expr1 = expr1;
            Op = natOperation;
            Expr2 = expr2;
        }
    }
}
