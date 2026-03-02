---
title: settings
id: 66b35d9648094e001dcdd04d
created_unix: 1723030936
updated_unix: 1723603332
views: 13
---

# settings


```style.css
@import "/api/code/wogikaze/settings/style.css";
@import "/api/code/villagepump/アイコン記法を画像記法っぽくするUserCSS/style.css";
.page-list-item.pin + .page-list-item:not(.pin) {
  clear: both;
}

 @media (hover: none) {
 	/* ピン留めするカードの数が偶数である限りは秩序が保たれる脆弱なCSS */
 	.page-list ul.grid {
		grid-template-columns: repeat(6, 1Fr);
	}
	.page-list > .grid li {
    	&.pin {
    		grid-column: 2 span;
    	}
    	&:not(.pin) {
    		&:nth-child(odd) {
        		grid-column: 1 / 4;
        	}
        	&:nth-child(even) {
        		grid-column: 4 / 7;
        	}
		}
	}
}
 .page-list > .grid li {
     &.pin {
     	height: 32px;
     	width: 100%;
     	margin-bottom: 5px;
     }
     &.page-list-item {
         &.pin a {
         	background-color: var(--card-bg);
         	border-radius: 7px;
         	margin: none;
         	box-shadow: none;
            .title {
            	font-size: 12px;
            	color: var(--card-title-color);
            	max-height: 20px;
            	text-align: center;
            }
            .content :is(.description,.icon) { display: none; }
         }
         a {
         	.header.pinned {
            	border-top:none;
            	padding: 6px 5px;
            }
            .pin {background: none;}
         }
    }
}



```
