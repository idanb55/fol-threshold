using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using FolThresholdParser.BapaFormula;
using FolThresholdParser.FolThresholdEntities;
using FolThresholdParser.Parser;
using FolThresholdParser.Utils;

namespace FolThresholdParser.FolSyntax
{
    public class Identifier
    {
        public bool Constant { get; protected set; }
        public string Name { get; protected set; }

        public Identifier(bool constant, string name)
        {
            Name = name;
            Constant = constant;
        }

        public static Identifier Parse(ArrayView<Token> tokens)
        {
            var constant = false;
            var tokenIndex = 0;
            if (tokens[tokenIndex].Type == SyntaxKind.ConstantKeyword)
            {
                constant = true;
                ++tokenIndex;
            }
            switch (tokens[tokenIndex].Type)
            {
                case SyntaxKind.NaturalKeyword:
                    return Natural.Parse(constant, tokens.Skip(tokenIndex + 1));
                case SyntaxKind.QuorumKeyword:
                    return Quorum.Parse(constant, tokens.Skip(tokenIndex + 1));
                default:
                    return null;
            }
        }

        private static readonly Regex BoundVariableNameRegex = new Regex("([a-z]*)([A-Z]*)([0-9]+)");

        public static Identifier GetIdentifier(Dictionary<string, Identifier> identifiers, string variable, out int index)
        {
            var match = BoundVariableNameRegex.Match(variable);
            if (!match.Success) throw new Exception($"Illegal variable name: {variable}");
            var existsName = match.Groups[1].Value;
            var forallName = match.Groups[2].Value;
            if (!string.IsNullOrEmpty(existsName) && !string.IsNullOrEmpty(forallName))
                throw new Exception($"Illegal variable name: {variable}");
            index = int.Parse(match.Groups[3].Value);
            if (!string.IsNullOrEmpty(existsName))
                return identifiers[existsName];
            if (!string.IsNullOrEmpty(forallName))
                return identifiers[forallName.ToLower()];
            throw new Exception($"Illegal variable name: {variable}");
        }

        public static BapaBind.BapaBindType BapaBindType(Dictionary<string, Identifier> identifiers, string variable)
        {
            var match = BoundVariableNameRegex.Match(variable);
            if (!match.Success) throw new Exception($"Illegal variable name: {variable}");
            var existsName = match.Groups[1].Value;
            var forallName = match.Groups[2].Value;
            if (!string.IsNullOrEmpty(existsName) && !string.IsNullOrEmpty(forallName))
                throw new Exception($"Illegal variable name: {variable}");
            BapaBind.BapaBindType type;
            if (!string.IsNullOrEmpty(existsName) && identifiers[existsName] is Natural)
                type = BapaBind.BapaBindType.Existsnat;
            else if (!string.IsNullOrEmpty(existsName) && identifiers[existsName] is Quorum)
                type = BapaBind.BapaBindType.Existsset;
            else if (!string.IsNullOrEmpty(forallName) && identifiers[forallName.ToLower()] is Natural)
                type = BapaBind.BapaBindType.Forallnat;
            else if (!string.IsNullOrEmpty(forallName) && identifiers[forallName.ToLower()] is Quorum)
                type = BapaBind.BapaBindType.Forallset;
            else
                throw new Exception($"Illegal variable name: {variable}");
            return type;
        }
    }

    public class Natural : Identifier
    {
        public Natural(bool constant, string name) : base(constant, name) { }

        public static Natural Parse(bool constant, ArrayView<Token> tokens)
        {
            var token = tokens.Single();
            if (token.Type != SyntaxKind.VariableNameToken) throw new ParserTokenException("Illegal natural number", token);
            return new Natural(constant, token.Value);
        }
    }

    public class Quorum : Identifier
    {
        public SyntaxKind Operation { get; protected set; }
        public NaturalExpression Expression { get; protected set; }

        public Quorum(bool constant, string name, SyntaxKind operation, NaturalExpression expression) : base(constant, name)
        {
            Operation = operation;
            Expression = expression;
        }

        public static Quorum Parse(bool constant, ArrayView<Token> tokens)
        {
            if (tokens[0].GeneralType != SyntaxGeneralType.VariableName) throw new ParserTokenException("Illegal quorum name", tokens[0]);
            if (tokens[1].GeneralType != SyntaxGeneralType.ComparisonOperators) throw new ParserTokenException("expected comparison operator", tokens[0]);
            return new Quorum(constant, tokens[0].Value, tokens[1].Type, NaturalExpression.Parse(tokens.Skip(2)));
        }

        /**public BapaFormula.BapaFormula GetQuorumAssumption(int index = 0)
        {
            var name = Name;
            if (!Constant) name += index;
            BapaFormula.BapaFormula formula = new BapaNatRelation(NaturalFormula.ToNatRelation(Operation), new BapaCard(new BapaSetVar(name)), Expression.ToBapaNatExpression());
            return formula;
        }**/
    }
}
