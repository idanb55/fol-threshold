using System;
using System.Collections.Generic;
using System.Linq;
using FolThresholdParser.Parser;
using FolThresholdParser.Utils;

namespace FolThresholdParser.FolSyntax
{
    public abstract class SetExpression
    {
        public abstract IEnumerable<string> VariablesToBind { get; }

        public static SetExpression Parse(ArrayView<Token> tokens)
        {
            var cursor = 0;
            SetExpression leftExpr = null;
            if (tokens[cursor].Type == SyntaxKind.OpenParenthesisToken)
            {
                var innerLength = tokens.Skip(cursor).IndexOfCloseParenthesis();
                leftExpr = Parse(tokens.Skip(1).Take(innerLength));
                cursor += innerLength + 1;
            }
            else if (tokens[cursor].Type == SyntaxKind.VariableNameToken)
            {
                var varName = tokens[cursor].Value;
                ++cursor;
                if (cursor < tokens.Length && tokens[cursor].Type == SyntaxKind.LiteralNumberToken)
                {
                    leftExpr = new SetVarInstanceExpression(varName, int.Parse(tokens[cursor].Value));
                    ++cursor;
                }
                else
                    leftExpr = new SetVarExpression(varName);
            }
            else if (tokens[cursor].Type == SyntaxKind.ComplementOperationToken)
            {
                ++cursor;
                if (tokens[cursor].Type == SyntaxKind.OpenParenthesisToken)
                {
                    var innerLength = tokens.Skip(cursor).IndexOfCloseParenthesis();
                    leftExpr = new SetComplementExpression(Parse(tokens.Skip(2).Take(innerLength)));
                    cursor += innerLength + 1;
                }
                else if (tokens[cursor].Type == SyntaxKind.VariableNameToken)
                {
                    var varName = tokens[cursor].Value;
                    ++cursor;
                    if (cursor < tokens.Length && tokens[cursor].Type == SyntaxKind.LiteralNumberToken)
                    {
                        leftExpr = new SetComplementExpression(new SetVarInstanceExpression(varName, int.Parse(tokens[cursor].Value)));
                        ++cursor;
                    }
                    else
                        leftExpr = new SetComplementExpression(new SetVarExpression(varName));
                }
            }

            if (cursor < tokens.Length && tokens[cursor].GeneralType != SyntaxGeneralType.SetOperators)
                throw new Exception("Illegal Set operator");

            return cursor >= tokens.Length
                ? leftExpr
                : new SetOpExpression(leftExpr, tokens[cursor].Type, Parse(tokens.Skip(cursor + 1)));
        }

        public abstract string ToIvyAxiom();
    }

    public class SetVarExpression : SetExpression
    {
        protected readonly string Name;

        public SetVarExpression(string name)
        {
            Name = name;
        }

        public override IEnumerable<string> VariablesToBind => new string[0];

        public override string ToIvyAxiom()
        {
            return $"{Name}(N)";
        }
    }

    public class SetVarInstanceExpression : SetExpression
    {
        protected readonly string Name;
        protected readonly int Index;

        private string FullName => $"{Name}{Index}";

        public SetVarInstanceExpression(string name, int index)
        {
            Name = name;
            Index = index;
        }

        public override IEnumerable<string> VariablesToBind => new[] { FullName };

        public override string ToIvyAxiom()
        {
            return $"member_{Name}(N, {FullName})";
        }
    }

    public class SetOpExpression : SetExpression
    {
        protected readonly SetExpression Expr1;
        protected readonly SyntaxKind Op;
        protected readonly SetExpression Expr2;

        public override IEnumerable<string> VariablesToBind => Expr1.VariablesToBind.Concat(Expr2.VariablesToBind);

        public SetOpExpression(SetExpression expr1, SyntaxKind setOperation, SetExpression expr2)
        {
            Expr1 = expr1;
            Op = setOperation;
            Expr2 = expr2;
        }

        public static SetExpression Aggregate(SyntaxKind setOperation, SetExpression[] expressions)
        {
            return expressions.Aggregate((expr1, expr2) => new SetOpExpression(expr1, setOperation, expr2));
        }

        enum SetRelation
        {
            Intersection, Union
        }

        private static SetRelation GetOperation(SyntaxKind op)
        {
            switch (op)
            {
                case SyntaxKind.AndOperationToken:
                    return SetRelation.Intersection;
                case SyntaxKind.OrOperationToken:
                    return SetRelation.Union;
                default:
                    throw new Exception("Illegal Natural operation");
            }
        }

        public override string ToIvyAxiom()
        {
            return $"{Expr1.ToIvyAxiom()} {Tokenizer.Keywords[Op]} {Expr2.ToIvyAxiom()})";
        }
    }

    public class SetComplementExpression : SetExpression
    {
        protected SetExpression Expr;

        public SetComplementExpression(SetExpression expr)
        {
            Expr = expr;
        }

        public override IEnumerable<string> VariablesToBind => Expr.VariablesToBind;

        public override string ToIvyAxiom()
        {
            return $"~{Expr.ToIvyAxiom()}";
        }
    }
}
