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
                    leftExpr = new SetComplementExpression(new SetVarExpression(varName));
                }
            }

            if (cursor < tokens.Length && tokens[cursor].GeneralType != SyntaxGeneralType.SetOperators)
                throw new Exception("Illegal Set operator");

            return cursor >= tokens.Length
                ? leftExpr
                : new SetOpExpression(leftExpr, tokens[cursor].Type, Parse(tokens.Skip(cursor + 1)));
        }

        public abstract string ToIvyAxiom(Dictionary<string, Identifier> identifiers);
        public abstract string GetSmtAssert(Dictionary<string, Identifier> identifiers);
    }

    public class SetVarExpression : SetExpression
    {
        protected readonly string Name;

        public SetVarExpression(string name)
        {
            Name = name;
        }

        public override IEnumerable<string> VariablesToBind => new string[0];

        public override string ToIvyAxiom(Dictionary<string, Identifier> identifiers)
        {
            if (!identifiers.ContainsKey(Name))
                throw new Exception($"Unknown identifier {Name}");
            if (identifiers[Name].Constant) return $"member_{Name.ToLower()}(N)";
            var identifier = identifiers[Name];
            return $"member_{identifier.Name.ToLower()}(N, {Name.ToUpper()})";
        }

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers)
        {
            if (!identifiers.ContainsKey(Name))
                throw new Exception($"Unknown identifier {Name}");
            if (identifiers[Name].Constant) return Name;
            return identifiers[Name].Name;
        }

        public override string ToString()
        {
            return Name;
        }
    }

    public class SetOpExpression : SetExpression
    {
        protected readonly SetExpression Expr1;
        protected readonly SetRelation Op;
        protected readonly SetExpression Expr2;

        public override IEnumerable<string> VariablesToBind => Expr1.VariablesToBind.Concat(Expr2.VariablesToBind);

        public SetOpExpression(SetExpression expr1, SyntaxKind setOperation, SetExpression expr2)
        {
            Expr1 = expr1;
            Op = (SetRelation)setOperation;
            Expr2 = expr2;
        }

        public static SetExpression Aggregate(SyntaxKind setOperation, SetExpression[] expressions)
        {
            return expressions.Aggregate((expr1, expr2) => new SetOpExpression(expr1, setOperation, expr2));
        }

        public  enum SetRelation
        {
            Intersection = SyntaxKind.AndOperationToken, Union = SyntaxKind.OrOperationToken
        }

        public override string ToIvyAxiom(Dictionary<string, Identifier> identifiers)
        {
            return $"{Expr1.ToIvyAxiom(identifiers)} {Tokenizer.Keywords[(SyntaxKind)Op]} {Expr2.ToIvyAxiom(identifiers)}";
        }

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers)
        {
            return
                $"({Op.ToString().ToLower()} {Expr1.GetSmtAssert(identifiers)} {Expr2.GetSmtAssert(identifiers)})";
        }

        public override string ToString()
        {
            return $"{Expr1} {Tokenizer.Keywords[(SyntaxKind)Op]} {Expr2}";
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

        public override string ToIvyAxiom(Dictionary<string, Identifier> identifiers)
        {
            return $"~{Expr.ToIvyAxiom(identifiers)}";
        }

        public override string GetSmtAssert(Dictionary<string, Identifier> identifiers)
        {
            return
                $"(setminus {FolThresholdSystem.FolThresholdSystem.UniversalSetIdentifier} {Expr.GetSmtAssert(identifiers)})";
        }

        public override string ToString()
        {
            return $"~{Expr}";
        }
    }
}
