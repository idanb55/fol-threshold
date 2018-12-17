using System;
using System.Runtime.Serialization;

namespace FolThresholdParser
{
    [Serializable]
    internal class IllegalNaturalName : Exception
    {
        private Token token;

        public IllegalNaturalName()
        {
        }

        public IllegalNaturalName(string message) : base(message)
        {
        }

        public IllegalNaturalName(Token token)
        {
            this.token = token;
        }

        public IllegalNaturalName(string message, Exception innerException) : base(message, innerException)
        {
        }

        protected IllegalNaturalName(SerializationInfo info, StreamingContext context) : base(info, context)
        {
        }
    }
}