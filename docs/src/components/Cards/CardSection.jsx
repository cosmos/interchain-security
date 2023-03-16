import React from 'react';
import Card from './Card';

function CardSection(props) {
  return (
    <div className="card-section grid grid-cols-1 lg:grid-cols-2 gap-4 no-underline">
      {props.cards.map((card, index) => {
        return (
          <Card
            key={index}
            href={card.href}
            header={card.header}
            summary={card.summary}
          />  
        )
      })}
    </div>
  )
}

export default CardSection;
