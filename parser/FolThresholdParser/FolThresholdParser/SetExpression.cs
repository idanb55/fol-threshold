using System;
using System.Collections.Generic;
using System.Linq;
using FolThresholdParser.Parser;

namespace FolThresholdParser
{
    public abstract class SetExpression : IExpression
    {
        public abstract IEnumerable<string> Variables { get; }

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
    }

    public class SetVarExpression : SetExpression
    {
        protected readonly string Name;

        public SetVarExpression(string name)
        {
            Name = name;
        }

        public override IEnumerable<string> Variables => new []{Name};
    }

    public class SetVarInstanceExpression : SetExpression
    {
        protected readonly string Name;
        protected readonly int Index;

        public SetVarInstanceExpression(string name, int index)
        {
            Name = name;
            Index = index;
        }

        public override IEnumerable<string> Variables => new[] { Name };
    }

    public class SetOpExpression : SetExpression
    {
        protected readonly SetExpression Expr1;
        protected readonly SyntaxKind Op;
        protected readonly SetExpression Expr2;

        public override IEnumerable<string> Variables => Expr1.Variables.Concat(Expr2.Variables);

        public SetOpExpression(SetExpression expr1, SyntaxKind setOperation, SetExpression expr2)
        {
            Expr1 = expr1;
            Op = setOperation;
            Expr2 = expr2;
        }
    }

    public class SetComplementExpression : SetExpression
    {
        protected SetExpression Expr;

        public SetComplementExpression(SetExpression expr)
        {
            Expr = expr;
        }

        public override IEnumerable<string> Variables => Expr.Variables;
    }
}
