import React from 'react';

function Card(props) {
  return (
    <a href={props.href} className="border shadow rounded-sm border-stone-200 dark:border-stone-800 dark:bg-neutral-900 hover:border-stone-300 hover:shadow-lg dark:hover:border-stone-200 transition-all duration-200 no-underline">
      <div className="p-6">
        <h2 className="">{props.header}</h2>
        <p className="">{props.summary}</p>
      </div>
    </a>
  )
}

export default Card;
